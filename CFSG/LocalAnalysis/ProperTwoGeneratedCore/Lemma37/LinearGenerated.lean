module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.LinearSetup
public import CFSG.StronglyEmbedded
public import CFSG.Models.BenderSuzuki

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly

theorem isBenderGroup_exists_fusionBenderBorel {X : Type*} [Group X] [Finite X]
    (h : CFSG.BenderSuzuki.IsBenderGroup X) : ∃ q k : ℕ, fusionBenderBorel X q k := by
  rcases h with ⟨n, hn, e⟩ | ⟨n, hn, e⟩ | ⟨n, hn, e⟩
  · have : Finite (CFSG.Theory.Comparator.PSL2Model n) := Finite.of_surjective e e.surjective
    exact ⟨_, _, (bender_psl2_borel_full n hn).map_mulEquiv e.symm⟩
  · have hmodel : CFSG.Theory.Comparator.SzModel n = Sz n := CFSG.Models.benderSzModel_eq_sz n
    let e' : X ≃* Sz n := e.trans (MulEquiv.subgroupCongr hmodel)
    have : Finite (Sz n) := Finite.of_surjective e' e'.surjective
    exact ⟨_, _, (bender_suzuki_borel_full n hn).map_mulEquiv e'.symm⟩
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hmodel : CFSG.Theory.Comparator.PSU3Model n = PSU3 2 n := CFSG.Models.benderPSU3Model_eq_psu3 n
    let e' : X ≃* PSU3 2 n := e.trans (MulEquiv.subgroupCongr hmodel)
    have : Finite (PSU3 2 n) := Finite.of_surjective e' e'.surjective
    exact ⟨_, _, (bender_psu3_borel_full n hn).map_mulEquiv e'.symm⟩

theorem involution_centralizer_le_of_fusionStronglyEmbedded {X : Type*} [Group X] [Finite X]
    {M : Subgroup X} (hM : fusionStronglyEmbedded M) {t : X} (htM : t ∈ M) (ht : orderOf t = 2) :
    Subgroup.centralizer ({t} : Set X) ≤ M := by
  intro c hc
  by_contra hcM
  have hodd := hM.2.2 c hcM
  have htc : t ∈ M ⊓ M.map (MulAut.conj c⁻¹).toMonoidHom := by
    refine ⟨htM, t, htM, ?_⟩
    have h := Subgroup.mem_centralizer_singleton_iff.mp hc
    change c⁻¹ * t * c⁻¹⁻¹ = t
    rw [inv_inv, mul_assoc, ← h, inv_mul_cancel_left]
  have hdvd := Subgroup.orderOf_dvd_natCard _ htc
  rw [ht] at hdvd
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)

theorem isSolvable_normalizer_sylow {X : Type*} [Group X] [Finite X] (P : Sylow 2 X) :
    Group.IsSolvable (Subgroup.normalizer ((P : Subgroup X) : Set X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := Subgroup.normalizer ((P : Subgroup X) : Set X)
  set P' := (P : Subgroup X).subgroupOf N
  have : P'.Normal := Subgroup.normal_in_normalizer
  have h2 : IsPGroup 2 P' := fun g => by
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨((g : N) : X), g.2⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    simpa using congrArg Subtype.val hk
  have : Group.IsNilpotent P' := h2.isNilpotent
  have hodd : Odd (Nat.card (N ⧸ P')) := by
    rw [← Subgroup.index]
    have h := Subgroup.relIndex_dvd_index_of_le
      (Subgroup.le_normalizer : (P : Subgroup X) ≤ Subgroup.normalizer ((P : Subgroup X) : Set X))
    exact Odd.of_dvd_nat (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp (Sylow.not_dvd_index P))) h
  have : Group.IsSolvable (N ⧸ P') := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  exact Group.isSolvable_of_ker_le_range P'.subtype (QuotientGroup.mk' P')
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {H : Subgroup G} {z : G}

theorem caseOne_generated_eq_top (hset : CoreSetting G S H)
    (hz : IsCentralInvolution (S : Subgroup G) z)
    (hesc : ¬ Subgroup.centralizer ({z} : Set G) ≤ H) {J : Subgroup (EscapingQuotient z)}
    (hJ : CFSG.IsComponent J) (hzJ : escapingBar z ∉ J)
    (htrans : ∀ a ∈ (S : Subgroup G), ∀ b ∈ (S : Subgroup G), a ≠ 1 → b ≠ 1 →
      ∃ n ∈ Subgroup.normalizer ((S : Subgroup G) : Set G), n⁻¹ * a * n = b) :
    properTwoGenCoreGamma (S : Subgroup G) 2 ⊔ Subgroup.centralizer ({z} : Set G) = ⊤ := by
  by_contra hne
  have : IsSimpleGroup G := hset.simple
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H₀ := properTwoGenCoreGamma (S : Subgroup G) 2 ⊔ Subgroup.centralizer ({z} : Set G)
  have hrank : 2 ≤ CFSG.Open.pRank 2 (S : Subgroup G) := by have := hset.rank; omega
  have hset₀ : CoreSetting G S H₀ := ⟨hset.simple, hset.nonabelian, hset.rank, hne,
    (sylow_le_gamma S hrank).trans le_sup_left, le_sup_left⟩
  have hNH₀ := coreSetting_sylow_normalizer_le hset₀
  have hCH₀ : Subgroup.centralizer ({z} : Set G) ≤ H₀ := le_sup_right
  have hz1 : z ≠ 1 := by
    rintro rfl
    have h := hz.2.1
    rw [orderOf_one] at h
    exact absurd h (by decide)
  have hconj : ∀ x ∈ H₀, orderOf x = 2 → ∃ h ∈ H₀, h⁻¹ * z * h = x := by
    intro x hx hx2
    obtain ⟨g, hg⟩ := exists_conj_mem_sylow (S.subtype hset₀.sylow_le)
      (isPGroup_zpowers_of_orderOf_eq_two (x := (⟨x, hx⟩ : H₀)) (by rw [Subgroup.orderOf_mk, hx2]))
    have hy := hg _ (Subgroup.mem_zpowers _)
    rw [Sylow.coe_subtype, Subgroup.mem_subgroupOf] at hy
    have hyS : (g : G)⁻¹ * x * g ∈ (S : Subgroup G) := by simpa using hy
    have hy1 : (g : G)⁻¹ * x * g ≠ 1 := by
      intro h
      have h2 := (orderOf_inv_mul_mul_eq x (g : G)).trans hx2
      rw [h, orderOf_one] at h2
      exact absurd h2 (by decide)
    obtain ⟨n, hn, hny⟩ := htrans z hz.1 _ hyS hz1 hy1
    refine ⟨n * (g : G)⁻¹, H₀.mul_mem (hNH₀ hn) (H₀.inv_mem g.2), ?_⟩
    calc (n * (g : G)⁻¹)⁻¹ * z * (n * (g : G)⁻¹) = (g : G) * (n⁻¹ * z * n) * (g : G)⁻¹ := by group
      _ = x := by rw [hny]; group
  have hSE : CFSG.BenderSuzuki.IsStronglyEmbeddedOrder H₀ := by
    refine ⟨hne, even_iff_two_dvd.mpr ?_, fun g hg => ?_⟩
    · have h := Subgroup.orderOf_dvd_natCard H₀
        (hCH₀ (Subgroup.mem_centralizer_singleton_iff.mpr rfl))
      rwa [hz.2.1] at h
    · by_contra hodd
      rw [Nat.not_odd_iff_even] at hodd
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp hodd)
      have hx2 : orderOf (x : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hx
      obtain ⟨y, hyH, hyx⟩ := Subgroup.mem_map.mp x.2.2
      have hyx' : g * y * g⁻¹ = x := hyx
      have hy2 : orderOf y = 2 := by
        rw [← hx2, ← hyx', ← orderOf_inv_mul_mul_eq y g⁻¹, inv_inv]
      obtain ⟨a, haH, hax⟩ := hconj _ x.2.1 hx2
      obtain ⟨b, hbH, hby⟩ := hconj y hyH hy2
      have hc : a * g * b⁻¹ ∈ Subgroup.centralizer ({z} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        have h2 : z = a * g * b⁻¹ * z * (a * g * b⁻¹)⁻¹ := by
          calc z = a * (a⁻¹ * z * a) * a⁻¹ := by group
            _ = a * (g * (b⁻¹ * z * b) * g⁻¹) * a⁻¹ := by rw [hax, hby, hyx']
            _ = a * g * b⁻¹ * z * (a * g * b⁻¹)⁻¹ := by group
        calc a * g * b⁻¹ * z = a * g * b⁻¹ * z * (a * g * b⁻¹)⁻¹ * (a * g * b⁻¹) := by group
          _ = z * (a * g * b⁻¹) := by rw [← h2]
      apply hg
      have hgeq : g = a⁻¹ * (a * g * b⁻¹) * b := by group
      rw [hgeq]
      exact H₀.mul_mem (H₀.mul_mem (H₀.inv_mem haH) (hCH₀ hc)) hbH
  obtain ⟨q, k, hB⟩ :=
    isBenderGroup_exists_fusionBenderBorel (CFSG.BenderSuzuki.bender_suzuki H₀ hSE)
  have hCN : Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer ((S : Subgroup G) : Set G) :=
    involution_centralizer_le_of_fusionStronglyEmbedded (hB S).1 (Subgroup.le_normalizer hz.1)
      hz.2.1
  have := isSolvable_normalizer_sylow S
  have : Group.IsSolvable (Subgroup.centralizer ({z} : Set G)) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hCN)
  have : Group.IsSolvable (EscapingQuotient z) :=
    Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective _)
  have : Group.IsSolvable J := Group.isSolvable_of_isSolvable_injective J.subtype_injective
  have := (caseOne_quotientData hset hz hesc).component_isSimpleGroup hJ hzJ
  have hcomm : ∀ a b : J, a * b = b * a := IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance
  obtain ⟨a, b, hab⟩ := hJ.1.2.2
  obtain ⟨a', rfl⟩ := QuotientGroup.mk'_surjective _ a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk'_surjective _ b
  exact hab (by rw [← map_mul, ← map_mul, hcomm a' b'])

end CFSG.ProperTwoGeneratedCore.Lemma37
