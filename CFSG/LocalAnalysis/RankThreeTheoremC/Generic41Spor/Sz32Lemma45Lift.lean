module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.TypeIILemma45Gen
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_10Lemmas
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_10Core
import CFSG.LocalAnalysis.RankThreeTheoremC.InvariantTwoBalance
import CFSG.LocalAnalysis.RankThreeUC.TheoremDClauseCCore

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3 (u3S u3T)

variable {G : Type} [Group G] [Finite G]

theorem szg_mem_of_normalizer_sylow {X : Type} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    {K : Subgroup X} (T' : Sylow p ↥K) {s : X} (hsK : s ∈ K) (hs : s ^ p = 1)
    (hn : s ∈ normalizer (((T' : Subgroup ↥K).map K.subtype : Subgroup X) : Set X)) :
    s ∈ (T' : Subgroup ↥K).map K.subtype := by
  set k : ↥K := ⟨s, hsK⟩ with hk
  have e1 : ∀ g : ↥K, (g : X) ∈ (T' : Subgroup ↥K).map K.subtype ↔ g ∈ (T' : Subgroup ↥K) :=
    fun g => Subgroup.mem_map_iff_mem K.subtype_injective
  have hkn' : k ∈ normalizer ((T' : Subgroup ↥K) : Set ↥K) := by
    rw [mem_normalizer_iff]
    intro h
    have h1 := (mem_normalizer_iff.mp hn (h : X))
    have e2 : s * (h : X) * s⁻¹ ∈ (T' : Subgroup ↥K).map K.subtype ↔
        k * h * k⁻¹ ∈ (T' : Subgroup ↥K) := e1 (k * h * k⁻¹)
    rw [← e1 h, ← e2]
    exact h1
  have hkn : k ∈ normalizer (T' : Set ↥K) := hkn'
  have hkp : IsPGroup p (Subgroup.zpowers k) := by
    have hk5 : k ^ p = 1 := Subtype.ext hs
    have hord : orderOf k ∣ p := orderOf_dvd_of_pow_eq_one hk5
    rcases (Nat.dvd_prime Fact.out).mp hord with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h]; simp)
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h]; simp)
  have := hkp.inf_normalizer_sylow T'
  have hmem : k ∈ Subgroup.zpowers k ⊓ normalizer (T' : Set ↥K) :=
    ⟨Subgroup.mem_zpowers k, hkn⟩
  rw [this] at hmem
  exact ⟨k, hmem.2, rfl⟩

theorem szg_sylow_image {p : ℕ} [Fact p.Prime] {J T : Subgroup G} {X : Type} [Group X] [Finite X]
    (π : ↥J →* X) (hT : IsSylowOf p T J) (R : Sylow p X)
    (hTR : (T.subgroupOf J).map π ≤ (R : Subgroup X)) :
    ∃ T' : Sylow p ↥π.range, (T' : Subgroup ↥π.range) = (T.subgroupOf J).map π.rangeRestrict ∧
      (T' : Subgroup ↥π.range).map π.range.subtype = (T.subgroupOf J).map π ∧
      (R : Subgroup X) ⊓ π.range = (T.subgroupOf J).map π := by
  set K : Subgroup X := π.range with hK
  let π' : ↥J →* ↥K := π.rangeRestrict
  have hπ' : Function.Surjective π' := π.rangeRestrict_surjective
  obtain ⟨Tsyl, hTsyl⟩ := hT.exists_sylow_eq_subgroupOf
  let T' : Sylow p ↥K := Tsyl.mapSurjective hπ'
  have hT'coe : (T' : Subgroup ↥K) = (Tsyl : Subgroup ↥J).map π' := Sylow.coe_mapSurjective hπ' Tsyl
  have hT'map : (T' : Subgroup ↥K).map K.subtype = (T.subgroupOf J).map π := by
    rw [hT'coe, Subgroup.map_map, hTsyl]
    rfl
  have hRK : (R : Subgroup X) ⊓ K = (T.subgroupOf J).map π := by
    have hSyl : IsSylowOf p ((T.subgroupOf J).map π) K := ⟨T', hT'map⟩
    refine hSyl.eq_of_le (le_inf hTR ?_) inf_le_right R.isPGroup'.to_inf_left
    rintro _ ⟨j, -, rfl⟩
    exact ⟨j, rfl⟩
  exact ⟨T', by rw [hT'coe, hTsyl], hT'map, hRK⟩

theorem szg_image_le_normalizer {p : ℕ} [Fact p.Prime] {J M T : Subgroup G}
    {X : Type} [Group X] [Finite X] (π : ↥J →* X)
    (hker : Nat.Coprime p (Nat.card π.ker)) (hkerM : ∀ j : ↥J, π j = 1 → (j : G) ∈ M)
    (hT : IsSylowOf p T J) (hNT : ∀ n : ↥J, (n : G) ∈ normalizer (T : Set G) → (n : G) ∈ M)
    (hJM : ¬ J ≤ M) (hmax : NormalizerMaximal p ↥π.range) (R : Sylow p X)
    (hTR : (T.subgroupOf J).map π ≤ (R : Subgroup X)) :
    (R : Subgroup X) ⊓ π.range = (T.subgroupOf J).map π ∧
      (M.subgroupOf J).map π ≤ normalizer (((R : Subgroup X) ⊓ π.range : Subgroup X) : Set X) := by
  set K : Subgroup X := π.range with hK
  let π' : ↥J →* ↥K := π.rangeRestrict
  have hπ' : Function.Surjective π' := π.rangeRestrict_surjective
  have hπ'ker : π'.ker = π.ker := MonoidHom.ker_rangeRestrict π
  obtain ⟨T', hT'coe, hT'map, hRK⟩ := szg_sylow_image π hT R hTR
  obtain ⟨Tsyl, hTsyl⟩ := hT.exists_sylow_eq_subgroupOf
  refine ⟨hRK, ?_⟩
  set H : Subgroup ↥K := (M.subgroupOf J).map π' with hH
  have hNH : normalizer (T' : Set ↥K) ≤ H := by
    intro q hq
    obtain ⟨j, rfl⟩ := hπ' q
    have hj : π' j ∈ normalizer (((T.subgroupOf J).map π' : Subgroup ↥K) : Set ↥K) := by
      rw [← hT'coe]; exact hq
    have hpg : IsPGroup p (T.subgroupOf J) := hTsyl ▸ Tsyl.isPGroup'
    obtain ⟨n, hn, hπn⟩ := typeII_frattini_ker π' (by rw [hπ'ker]; exact hker) hpg hj
    have hnG : (n : G) ∈ normalizer (((T.subgroupOf J : Subgroup ↥J).map J.subtype : Subgroup G) : Set G) :=
      u3main_mem_normalizer_map hn
    rw [Subgroup.map_subgroupOf_eq_of_le hT.le] at hnG
    exact ⟨n, Subgroup.mem_subgroupOf.mpr (hNT n hnG), hπn⟩
  have hHtop : H ≠ ⊤ := by
    intro htop
    apply hJM
    intro g hg
    have hmem : π' ⟨g, hg⟩ ∈ H := htop ▸ Subgroup.mem_top _
    obtain ⟨m, hm, hmg⟩ := hmem
    have hmg' : π m = π ⟨g, hg⟩ := congrArg Subtype.val hmg
    have hk : m⁻¹ * ⟨g, hg⟩ ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hmg', inv_mul_cancel]
    have h1 : ((m⁻¹ * ⟨g, hg⟩ : ↥J) : G) ∈ M := hkerM _ hk
    have h2 : (m : G) ∈ M := Subgroup.mem_subgroupOf.mp hm
    have : g = (m : G) * ((m⁻¹ * ⟨g, hg⟩ : ↥J) : G) := by simp
    rw [this]
    exact M.mul_mem h2 h1
  have hHeq : H = normalizer (T' : Set ↥K) := (hmax T' H hNH).resolve_right hHtop
  intro v hv
  obtain ⟨j, hj, rfl⟩ := hv
  have h1 : π' j ∈ H := ⟨j, hj, rfl⟩
  rw [hHeq] at h1
  have h2 := u3main_mem_normalizer_map h1
  rw [hT'map, ← hRK] at h2
  exact h2

theorem szg_lemma45_lift {Typ : ℕ → ∀ (Q : Type) [Group Q], Prop}
    {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G} {J : Subgroup G}
    (hS : Setting G) (hD1 : TheoremD1 G)
    (hX45 : Lemma45Facts Typ p Sz32Shape)
    (hmax : ∀ (K : Type) [Group K] [Finite K], Typ p K → NormalizerMaximal p K)
    (hiso : ∀ (A B : Type) [Group A] [Group B], A ≃* B → Typ p A → Typ p B)
    (hc : PointConfig Typ G p P M x J)
    (hNT : ∀ n : ↥J, (n : G) ∈ normalizer ((u3T P x J : Subgroup G) : Set G) → (n : G) ∈ M)
    (hTc : ∀ s ∈ u3T P x J, ∀ t ∈ u3T P x J, s * t = t * s)
    {U : Subgroup G} (hUe : IsElemAbelian p U) (hUcard : Nat.card U = p ^ 2) (hUS : U ≤ u3S P x)
    (hxU : x ∈ U) (hu : ∃ u ∈ U, ∃ t ∈ u3T P x J, u * t * u⁻¹ ≠ t) :
    ∃ S₁ : Subgroup G, rankTwoMaximalInvariantTwoSubgroup U S₁ ∧ ¬ S₁ ≤ M := by
  have hp : p.Prime := hc.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by have := hc.five; omega
  set C : Subgroup G := Subgroup.centralizer ({x} : Set G) with hC
  have hJC : J ≤ C := hc.le_cent
  have hCJ : C ≤ Subgroup.normalizer (J : Set G) := hc.cent_le
  set N₀ : Subgroup G := rankThreePrimeCore p J with hN₀
  have hN₀J : N₀ ≤ J := CFSG.AGLEmbedding.glbPrimeCore_le p J
  have hN₀cop : p.Coprime (Nat.card N₀) := CFSG.AGLEmbedding.glbPrimeCore_coprime p J
  have hJN : J ≤ normalizer (N₀ : Set G) := (CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec p J).2.1
  have hCN : C ≤ normalizer (N₀ : Set G) := by
    intro g hg
    have hgJ : J.map (MulAut.conj g).toMonoidHom = J :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hCJ hg)
    have h1 := glbPrimeCore_map_automorphism p J (MulAut.conj g)
    rw [hgJ] at h1
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h1
  obtain ⟨Q, hQg, ψ, hψ, hker, hQ⟩ := hc.typ
  haveI : Finite Q := Finite.of_surjective ψ hψ
  have hZ : Subgroup.center Q = ⊥ := u3main_center_bot hN₀J hc.perfect hc.lt hc.minimal ψ hψ hker
  obtain ⟨X, hXg, hXf, ρ, hρ, hρker⟩ := typeII_exists_reduction (C := C) (J := J) (N₀ := N₀) hCJ hCN
  have hJc : ∀ c ∈ C, ∀ j ∈ J, c * j * c⁻¹ ∈ J := fun c hc' j hj =>
    (mem_normalizer_iff.mp (hCJ hc') j).mp hj
  let π : ↥J →* X := ρ.comp (Subgroup.inclusion hJC)
  have hπ : ∀ j : ↥J, π j = ρ ⟨j, hJC j.2⟩ := fun j => rfl
  set K : Subgroup X := π.range with hK
  have hπ1 : ∀ j : ↥J, π j = 1 ↔ (j : G) ∈ N₀ := by
    intro j
    rw [hπ, hρker]
    constructor
    · intro h
      have hcen : ψ j ∈ Subgroup.center Q := by
        rw [Subgroup.mem_center_iff]
        intro q
        obtain ⟨j', rfl⟩ := hψ q
        have hmem : (j * j' * j⁻¹ * j'⁻¹ : ↥J) ∈ ψ.ker := by
          rw [hker, Subgroup.mem_subgroupOf]
          have := h j' j'.2
          simpa using this
        have h0 := MonoidHom.mem_ker.mp hmem
        simp only [map_mul, map_inv] at h0
        exact (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h0)).symm
      rw [hZ, Subgroup.mem_bot] at hcen
      have : j ∈ ψ.ker := hcen
      rw [hker, Subgroup.mem_subgroupOf] at this
      exact this
    · intro h j' hj'
      have h1 : j' * (j : G)⁻¹ * j'⁻¹ ∈ N₀ := (mem_normalizer_iff.mp (hJN hj') _).mp (N₀.inv_mem h)
      have := N₀.mul_mem h h1
      simpa [mul_assoc] using this
  have hπker : π.ker = N₀.subgroupOf J := by
    ext j
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hπ1 j
  have hkerπ : Nat.Coprime p (Nat.card π.ker) := by
    rw [hπker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN₀J).toEquiv]
    exact hN₀cop
  haveI hKn : K.Normal := ⟨by
    rintro _ ⟨j, rfl⟩ g
    obtain ⟨d, rfl⟩ := hρ g
    refine ⟨⟨(d : G) * j * (d : G)⁻¹, hJc d d.2 j j.2⟩, ?_⟩
    have e : (⟨(d : G) * j * (d : G)⁻¹, hJC (hJc d d.2 j j.2)⟩ : ↥C) =
        d * ⟨j, hJC j.2⟩ * d⁻¹ := Subtype.ext rfl
    show ρ ⟨(d : G) * j * (d : G)⁻¹, hJC (hJc d d.2 j j.2)⟩ = ρ d * ρ ⟨j, hJC j.2⟩ * (ρ d)⁻¹
    rw [e, map_mul, map_mul, map_inv]⟩
  have hKc : Subgroup.centralizer (K : Set X) = ⊥ := by
    rw [eq_bot_iff]
    intro a ha'
    obtain ⟨c, rfl⟩ := hρ a
    rw [Subgroup.mem_bot, hρker]
    intro j hj
    have hmem : (c : G) * j * (c : G)⁻¹ * j⁻¹ ∈ J := J.mul_mem (hJc c c.2 j hj) (J.inv_mem hj)
    have h1 := Subgroup.mem_centralizer_iff.mp ha' (π ⟨j, hj⟩) ⟨⟨j, hj⟩, rfl⟩
    have h1' : ρ ⟨j, hJC hj⟩ * ρ c = ρ c * ρ ⟨j, hJC hj⟩ := h1
    have h2 : π ⟨_, hmem⟩ = 1 := by
      show ρ ⟨(c : G) * j * (c : G)⁻¹ * j⁻¹, hJC hmem⟩ = 1
      have e : (⟨(c : G) * j * (c : G)⁻¹ * j⁻¹, hJC hmem⟩ : ↥C) =
          c * ⟨j, hJC hj⟩ * c⁻¹ * ⟨j, hJC hj⟩⁻¹ := Subtype.ext rfl
      rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, ← h1']
      group
    exact (hπ1 ⟨_, hmem⟩).mp h2
  have hkerEq : ψ.ker = π.ker := by rw [hker, hπker]
  let eK : Q ≃* ↥K :=
    (QuotientGroup.quotientKerEquivOfSurjective ψ hψ).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hkerEq).trans (QuotientGroup.quotientKerEquivRange π))
  have hKT : Typ p ↥K := hiso Q ↥K eK hQ
  have hSC : u3S P x ≤ C := inf_le_right
  let S'' : Subgroup X := (ρ.comp (Subgroup.inclusion hSC)).range
  have hS''p : IsPGroup p S'' := by
    have hSp : IsPGroup p ↥(u3S P x) := P.isPGroup'.to_inf_left
    exact hSp.of_surjective (ρ.comp (Subgroup.inclusion hSC)).rangeRestrict
      (MonoidHom.rangeRestrict_surjective _)
  obtain ⟨R, hR⟩ := hS''p.exists_le_sylow
  have hTS : u3T P x J ≤ u3S P x := inf_le_left
  have hTJ : u3T P x J ≤ J := inf_le_right
  have hTR : ((u3T P x J).subgroupOf J).map π ≤ (R : Subgroup X) := by
    rintro _ ⟨j, hj, rfl⟩
    exact hR ⟨⟨j, hTS (Subgroup.mem_subgroupOf.mp hj)⟩, rfl⟩
  have hTP : u3T P x J ≤ (P : Subgroup G) := inf_le_left.trans inf_le_left
  have hTp : IsPGroup p (u3T P x J) := P.isPGroup'.to_le hTP
  have hN₀M : N₀ ≤ M :=
    (u3main_core_facts hS hD1 hc.sigma hc.core hc.generic hc.le_cent hc.cent_le).1
  have hTsyl : IsSylowOf p (u3T P x J) J := hc.generic.2.2.1.inf_of_le_normalizer hJC hCJ
  obtain ⟨hRK, hMN⟩ := szg_image_le_normalizer π hkerπ (fun j hj => hN₀M ((hπ1 j).mp hj)) hTsyl hNT
    hc.not_le (hmax _ hKT) R hTR

  have hUC : U ≤ C := hUS.trans inf_le_right
  let U₀ : Subgroup X := (ρ.comp (Subgroup.inclusion hUC)).range
  have hU₀R : U₀ ≤ (R : Subgroup X) := by
    rintro _ ⟨u, rfl⟩
    exact hR ⟨⟨u, hUS u.2⟩, rfl⟩
  have hU₀e : IsElemAbelian p U₀ := typeII_isElemAbelian_range hUe _
  have hx1 : x ≠ 1 := hc.generic.2.1.2.1
  have hcop : ¬ p ∣ Nat.card π.ker := (hp.coprime_iff_not_dvd).mp hkerπ
  have hconj : ∀ (g : ↥C) (j : ↥J),
      π ⟨(g : G) * (j : G) * (g : G)⁻¹, hJc g g.2 j j.2⟩ = ρ g * π j * (ρ g)⁻¹ := by
    intro g j
    have hmem := hJc g g.2 j j.2
    show ρ ⟨(g : G) * (j : G) * (g : G)⁻¹, hJC hmem⟩ = _
    have e2 : (⟨(g : G) * (j : G) * (g : G)⁻¹, hJC hmem⟩ : ↥C) = g * ⟨j, hJC j.2⟩ * g⁻¹ :=
      Subtype.ext rfl
    rw [e2, map_mul, map_mul, map_inv]
    rfl
  have hstab : ∀ w ∈ u3S P x, ∀ t ∈ u3T P x J, w * t * w⁻¹ ∈ u3T P x J := by
    intro w hw t ht
    refine ⟨(u3S P x).mul_mem ((u3S P x).mul_mem hw (hTS ht)) ((u3S P x).inv_mem hw), ?_⟩
    exact hJc w (hSC hw) t (hTJ ht)
  have hfwd : ∀ (w : G) (hw : w ∈ u3S P x), ∀ h ∈ ((u3T P x J).subgroupOf J).map π,
      ρ ⟨w, hSC hw⟩ * h * (ρ ⟨w, hSC hw⟩)⁻¹ ∈ ((u3T P x J).subgroupOf J).map π := by
    intro w hw h hh
    obtain ⟨t, ht, rfl⟩ := hh
    refine ⟨⟨w * (t : G) * w⁻¹, hJc w (hSC hw) t t.2⟩, ?_, hconj ⟨w, hSC hw⟩ t⟩
    exact Subgroup.mem_subgroupOf.mpr (hstab w hw t (Subgroup.mem_subgroupOf.mp ht))
  have hsn : ∀ (w : G) (hw : w ∈ u3S P x),
      ρ ⟨w, hSC hw⟩ ∈ normalizer ((((u3T P x J).subgroupOf J).map π : Subgroup X) : Set X) := by
    intro w hw
    rw [mem_normalizer_iff]
    intro h
    refine ⟨fun hh => hfwd w hw h hh, fun hh => ?_⟩
    have h1 := hfwd w⁻¹ ((u3S P x).inv_mem hw) _ hh
    have e : (⟨w⁻¹, hSC ((u3S P x).inv_mem hw)⟩ : ↥C) = (⟨w, hSC hw⟩ : ↥C)⁻¹ := Subtype.ext rfl
    rw [e, map_inv, inv_inv] at h1
    simpa [mul_assoc] using h1
  obtain ⟨u, huU, t₁, ht₁T, hut⟩ := hu
  have huC : u ∈ C := hUC huU
  have hρu : ρ ⟨u, huC⟩ ∉ K := by
    intro hρK
    obtain ⟨T', hT'coe, hT'map, -⟩ := szg_sylow_image π hTsyl R hTR
    have hs5 : (ρ ⟨u, huC⟩) ^ p = 1 := by
      rw [← map_pow]
      have : (⟨u, huC⟩ : ↥C) ^ p = 1 := Subtype.ext (hUe.2 u huU)
      rw [this, map_one]
    have hmem := szg_mem_of_normalizer_sylow T' hρK hs5
      (by rw [hT'map]; exact hsn u (hUS huU))
    rw [hT'map] at hmem
    obtain ⟨t₀, ht₀, hπt₀⟩ := hmem
    have ht₁J : t₁ ∈ J := hTJ ht₁T
    have hwJ : u * t₁ * u⁻¹ ∈ J := hJc u huC t₁ ht₁J
    have ht₀T : (t₀ : G) ∈ u3T P x J := Subgroup.mem_subgroupOf.mp ht₀
    have h1 : π ⟨u * t₁ * u⁻¹, hwJ⟩ = π ⟨t₁, ht₁J⟩ := by
      rw [hconj ⟨u, huC⟩ ⟨t₁, ht₁J⟩, ← hπt₀, ← map_inv, ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      show (t₀ : G) * t₁ * (t₀ : G)⁻¹ = t₁
      exact mul_inv_eq_iff_eq_mul.mpr (hTc _ ht₀T t₁ ht₁T)
    have hw'T : (⟨u * t₁ * u⁻¹, hwJ⟩ * ⟨t₁, ht₁J⟩⁻¹ : ↥J) ∈ (u3T P x J).subgroupOf J := by
      refine Subgroup.mul_mem _ ?_ (Subgroup.inv_mem _ ?_)
      · exact Subgroup.mem_subgroupOf.mpr (hstab u (hUS huU) t₁ ht₁T)
      · exact Subgroup.mem_subgroupOf.mpr ht₁T
    have h2 := u3main_eq_one_of_ker π hcop (hTp.comap_subtype (K := J)) _ hw'T
      (by rw [map_mul, map_inv, h1, mul_inv_cancel])
    apply hut
    have h3 : (⟨u * t₁ * u⁻¹, hwJ⟩ : ↥J) = ⟨t₁, ht₁J⟩ := mul_inv_eq_one.mp h2
    exact congrArg Subtype.val h3
  have hU₀card : Nat.card U₀ = p := by
    refine typeII_card_range_eq hp (ρ.comp (Subgroup.inclusion hUC)) hUcard
      (a := ⟨x, hxU⟩) (fun h => hx1 (congrArg Subtype.val h)) ?_ (b := ⟨u, huU⟩) ?_
    · show ρ ⟨x, hUC hxU⟩ = 1
      rw [hρker]
      intro j hj
      have hxj : x * j = j * x := (Subgroup.mem_centralizer_singleton_iff.mp (hJC hj)).symm
      have : x * j * x⁻¹ * j⁻¹ = 1 := by
        rw [hxj]; group
      simp [this]
    · intro h
      have h' : ρ ⟨u, huC⟩ = 1 := h
      exact hρu (by rw [h']; exact K.one_mem)
  have hshape : Sz32Shape K (R : Subgroup X) U₀ := fun hle => hρu (hle ⟨⟨u, huU⟩, rfl⟩)
  obtain ⟨V, hVK, hV2, hU₀V, hnotV⟩ := hX45 X K ⟨hKn, hKc, hKT⟩ R U₀ hU₀R hU₀e hU₀card hshape
  refine typeII_exists_rankTwoMaximal_of_reduced hp hp2 (P.isPGroup'.to_le (hUS.trans inf_le_left))
    π hkerπ V hV2 hVK ?_ ?_
  · intro u hu j hj
    have huC : u ∈ C := hUC hu
    have hmem : u * (j : G) * u⁻¹ ∈ J := hJc u huC j j.2
    refine ⟨hmem, ?_⟩
    have hnorm : ρ ⟨u, huC⟩ ∈ normalizer (V : Set X) := hU₀V ⟨⟨u, hu⟩, rfl⟩
    have h1 := (mem_normalizer_iff.mp hnorm (π j)).mp hj
    have e : π ⟨u * (j : G) * u⁻¹, hmem⟩ = ρ ⟨u, huC⟩ * π j * (ρ ⟨u, huC⟩)⁻¹ := by
      show ρ ⟨u * (j : G) * u⁻¹, hJC hmem⟩ = _
      have e2 : (⟨u * (j : G) * u⁻¹, hJC hmem⟩ : ↥C) = ⟨u, huC⟩ * ⟨j, hJC j.2⟩ * ⟨u, huC⟩⁻¹ :=
        Subtype.ext rfl
      rw [e2, map_mul, map_mul, map_inv]
      rfl
    rw [e]
    exact h1
  · intro hle
    exact hnotV (hle.trans hMN)

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
