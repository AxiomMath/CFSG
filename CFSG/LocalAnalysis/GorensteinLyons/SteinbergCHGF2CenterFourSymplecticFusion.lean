module

public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBKGF2CriticalCenterExponentFour
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergCCCenterSymplectic
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBYNonfusedCoreInvolution
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GorensteinLyons

open Subgroup CFSG.Open
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.ComponentInitial (bilinIsometryGroup)
open scoped IsMulCommutative commutatorElement

namespace SteinbergCH

theorem isElementaryAbelian_of_mulEquiv {X Y : Type*} [Group X] [Group Y] {p : ℕ} (e : X ≃* Y)
    [hY : CFSG.IsElementaryAbelian p Y] : CFSG.IsElementaryAbelian p X :=
  CFSG.IsElementaryAbelian.of_mulEquiv e.symm inferInstance

theorem core_symplectic_package {G : Type*} [Group G] [Finite G] {M B : Subgroup G}
    (hBM : B ≤ M) (hcharM : IsCharacteristicP 2 M) (hBodd : Odd (Nat.card B))
    (hQnab : ∃ x y : CFSG.pCore 2 M, x * y ≠ y * x) [hcyc : IsCyclic (center (CFSG.pCore 2 M))]
    [hVel : CFSG.IsElementaryAbelian 2 (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))] {z : G}
    {z₀ : CFSG.pCore 2 M} (hz₀G : ((z₀ : M) : G) = z) (hz₀Z : z₀ ∈ center (CFSG.pCore 2 M))
    (hz₀ord : orderOf z₀ = 2) :
    (∃! v : ℕ, 1 ≤ v ∧ Module.finrank (ZMod 2)
      (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) = 2 * v) ∧
    ∃ b : LinearMap.BilinForm (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))),
      (∀ x y : CFSG.pCore 2 M, (((⁅x, y⁆ : CFSG.pCore 2 M) : M) : G) =
        z ^ (b (Additive.ofMul (x : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))
          (Additive.ofMul (y : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))).val) ∧
      (∀ b' : LinearMap.BilinForm (ZMod 2)
          (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))),
        (∀ x y : CFSG.pCore 2 M, (((⁅x, y⁆ : CFSG.pCore 2 M) : M) : G) =
          z ^ (b' (Additive.ofMul (x : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))
            (Additive.ofMul (y : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))).val) →
        b' = b) ∧
      b.IsAlt ∧ b.Nondegenerate ∧
      ∃ ρ : M →* LinearMap.GeneralLinearGroup (ZMod 2)
          (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))),
        (∀ (h : M) (x y : CFSG.pCore 2 M), (y : M) = h * x * h⁻¹ →
          ((ρ h : LinearMap.GeneralLinearGroup (ZMod 2)
              (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))) :
            Module.End (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))))
              (Additive.ofMul (x : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) =
            Additive.ofMul (y : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) ∧
        ρ.ker = CFSG.pCore 2 M ∧ (∀ h, ρ h ∈ bilinIsometryGroup b) ∧
        (∃ ι : M ⧸ CFSG.pCore 2 M →* bilinIsometryGroup b, Function.Injective ι ∧
          ∀ h : M, ((ι (h : M ⧸ CFSG.pCore 2 M) : bilinIsometryGroup b) :
            LinearMap.GeneralLinearGroup (ZMod 2)
              (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))) = ρ h) ∧
        ∀ x (hx : x ∈ B), ρ ⟨x, hBM hx⟩ = 1 → x = 1 := by
  obtain ⟨-, hdim, b, hrule, huniqb, hbalt, hbnd, ρ, hρ, hker, hiso, hι, hodd⟩ :=
    cyclic_center_two_core_faithful_symplectic_action (H := M) hcharM hQnab hz₀Z hz₀ord
  have hcoe : ∀ k : ℕ, (((z₀ ^ k : CFSG.pCore 2 M) : M) : G) = z ^ k := fun k => by
    rw [SubgroupClass.coe_pow, SubgroupClass.coe_pow, hz₀G]
  refine ⟨hdim, b, fun x y => ?_, fun b' hb' => huniqb b' fun x y => ?_, hbalt, hbnd, ρ, hρ, hker,
    hiso, hι, fun x hx h1 => ?_⟩
  · exact (congrArg (fun w : CFSG.pCore 2 M => ((w : M) : G)) (hrule x y)).trans (hcoe _)
  · exact Subtype.val_injective (Subtype.val_injective ((hb' x y).trans (hcoe _).symm))
  · have hBinj := hodd (B.subgroupOf M)
      (by rwa [Nat.card_congr (subgroupOfEquivOfLe hBM).toEquiv])
    have h2 : (ρ.comp (B.subgroupOf M).subtype) ⟨⟨x, hBM hx⟩, mem_subgroupOf.mpr hx⟩ =
        (ρ.comp (B.subgroupOf M).subtype) 1 := by
      rw [map_one]
      exact h1
    exact congrArg (fun y : B.subgroupOf M => ((y : M) : G)) (hBinj h2)

theorem core_symplectic_transport {G : Type*} [Group G] [Finite G] {M B Q : Subgroup G}
    (hBM : B ≤ M) (hcharM : IsCharacteristicP 2 M) (hBodd : Odd (Nat.card B))
    (hQ : Q = CFSG.inSubgroup (CFSG.pCore 2) M) (hcyc : IsCyclic (center Q))
    (hVel : CFSG.IsElementaryAbelian 2 (Q ⧸ center Q)) {z : G}
    (hzZ : z ∈ (center Q).map Q.subtype) (hzord : orderOf z = 2) (hQ' : ⁅Q, Q⁆ = zpowers z) :
    ∃ (_ : CFSG.IsElementaryAbelian 2 (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))),
      (∃! v : ℕ, 1 ≤ v ∧ Module.finrank (ZMod 2)
        (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) = 2 * v) ∧
      ∃ b : LinearMap.BilinForm (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))),
        (∀ x y : CFSG.pCore 2 M, (((⁅x, y⁆ : CFSG.pCore 2 M) : M) : G) =
          z ^ (b (Additive.ofMul (x : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))
            (Additive.ofMul (y : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))).val) ∧
        (∀ b' : LinearMap.BilinForm (ZMod 2)
            (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))),
          (∀ x y : CFSG.pCore 2 M, (((⁅x, y⁆ : CFSG.pCore 2 M) : M) : G) =
            z ^ (b' (Additive.ofMul (x : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))
              (Additive.ofMul (y : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))).val) →
          b' = b) ∧
        b.IsAlt ∧ b.Nondegenerate ∧
        ∃ ρ : M →* LinearMap.GeneralLinearGroup (ZMod 2)
            (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))),
          (∀ (h : M) (x y : CFSG.pCore 2 M), (y : M) = h * x * h⁻¹ →
            ((ρ h : LinearMap.GeneralLinearGroup (ZMod 2)
                (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))) :
              Module.End (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))))
                (Additive.ofMul (x : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) =
              Additive.ofMul (y : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) ∧
          ρ.ker = CFSG.pCore 2 M ∧ (∀ h, ρ h ∈ bilinIsometryGroup b) ∧
          (∃ ι : M ⧸ CFSG.pCore 2 M →* bilinIsometryGroup b, Function.Injective ι ∧
            ∀ h : M, ((ι (h : M ⧸ CFSG.pCore 2 M) : bilinIsometryGroup b) :
              LinearMap.GeneralLinearGroup (ZMod 2)
                (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))) = ρ h) ∧
          ∀ x (hx : x ∈ B), ρ ⟨x, hBM hx⟩ = 1 → x = 1 := by
  have hzQ : z ∈ Q := map_subtype_le _ hzZ
  have hzne : z ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hzord
    exact absurd hzord (by norm_num)
  obtain ⟨e, heval⟩ : ∃ e : CFSG.pCore 2 M ≃* Q,
      ∀ x : CFSG.pCore 2 M, ((e x : Q) : G) = ((x : M) : G) := by
    subst hQ
    exact ⟨(CFSG.pCore 2 M).equivMapOfInjective M.subtype M.subtype_injective, fun _ => rfl⟩
  have hcycQ₀ : IsCyclic (center (CFSG.pCore 2 M)) :=
    isCyclic_of_surjective (Subgroup.centerCongr e).symm.toMonoidHom (MulEquiv.surjective _)
  have hVel₀ : CFSG.IsElementaryAbelian 2 (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)) :=
    isElementaryAbelian_of_mulEquiv (QuotientGroup.congr _ _ e (map_center_eq e))
  have hQnab : ∃ x y : CFSG.pCore 2 M, x * y ≠ y * x := by
    by_contra hall
    push Not at hall
    apply hzne
    have h1 : ⁅Q, Q⁆ = ⊥ := by
      rw [commutator_eq_bot_iff_le_centralizer]
      intro a ha
      rw [mem_centralizer_iff]
      intro c hc
      have h2 := congrArg (fun x => ((e x : Q) : G)) (hall (e.symm ⟨c, hc⟩) (e.symm ⟨a, ha⟩))
      simpa using h2
    rw [hQ'] at h1
    exact zpowers_eq_bot.mp h1
  obtain ⟨z₀, hz₀⟩ : ∃ z₀ : CFSG.pCore 2 M, z₀ = e.symm ⟨z, hzQ⟩ := ⟨_, rfl⟩
  have hz₀G : ((z₀ : M) : G) = z := by
    rw [hz₀]
    have h1 := heval (e.symm ⟨z, hzQ⟩)
    rw [MulEquiv.apply_symm_apply] at h1
    exact h1.symm
  have hz₀Z : z₀ ∈ center (CFSG.pCore 2 M) := by
    obtain ⟨c, hc, hcz⟩ := hzZ
    have hc' : (⟨z, hzQ⟩ : Q) = c := Subtype.ext hcz.symm
    rw [hz₀, hc', ← map_center_eq e.symm]
    exact mem_map_of_mem _ hc
  have hz₀ord : orderOf z₀ = 2 := by
    rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe, hz₀G, hzord]
  exact ⟨hVel₀, core_symplectic_package (hcyc := hcycQ₀) (hVel := hVel₀) hBM hcharM hBodd hQnab
    hz₀G hz₀Z hz₀ord⟩

theorem core_fusion_package {G : Type*} [Group G] [Finite G] (hchar : IsCharacteristicPType G 2)
    {z : G} (hz : orderOf z = 2) {M Q : Subgroup G} (hM : M = centralizer ({z} : Set G))
    (hcharM : IsCharacteristicP 2 M) (hQ : Q = CFSG.inSubgroup (CFSG.pCore 2) M)
    (hΦ : (frattini Q).map Q.subtype = zpowers z) (hQ' : ⁅Q, Q⁆ = zpowers z)
    (hZ : IsCyclic (center Q)) (hSyl : ∃ S : Sylow 2 G, (S : Subgroup G) ≤ M)
    (hzZ : z ∈ (center Q).map Q.subtype)
    (huniq : ∀ y ∈ (center Q).map Q.subtype, orderOf y = 2 → y = z) :
    (∀ L : Subgroup G, L ≤ Q → L.relIndex Q = 2 → ∀ x ∈ centralizer (L : Set G),
      orderOf x = 2 → x ∈ L) ∧
    (∀ t ∈ Q, t ∉ (center Q).map Q.subtype → orderOf t = 2 →
      (Q ⊓ centralizer ({t} : Set G)).relIndex Q = 2 ∧
      (center ↥(Q ⊓ centralizer ({t} : Set G))).map (Q ⊓ centralizer ({t} : Set G)).subtype =
        (center Q).map Q.subtype ⊔ zpowers t ∧
      (∃ q ∈ Q, q * t * q⁻¹ = t * z) ∧
      ((∃ g : G, g⁻¹ * z * g = t) ↔
        ∃ g : G, g ∉ M ∧ Q ⊓ centralizer ({t} : Set G) ≤ conjugate M g) ∧
      ((¬ ∃ g : G, g⁻¹ * z * g = t) →
        {w | ∃ g : G, g⁻¹ * z * g = w} ∩
            (centralizer ((Q ⊓ centralizer ({t} : Set G) : Subgroup G) : Set G) : Set G) =
          {z} ∧
        normalizer ((Q ⊓ centralizer ({t} : Set G) : Subgroup G) : Set G) ≤ M ∧
        z ∈ CFSG.inSubgroup (CFSG.pCore 2) (centralizer ({t} : Set G)))) ∧
    ({w | ∃ g : G, g⁻¹ * z * g = w} ∩ (Q : Set G) = {z} →
      ∀ t ∈ Q, orderOf t = 2 → z ∈ CFSG.inSubgroup (CFSG.pCore 2) (centralizer ({t} : Set G))) := by
  obtain ⟨hidx2, hinv⟩ :=
    nonfused_core_involution_global_centralizer_control hz hM hcharM hQ hΦ hQ' hZ hSyl
  have hO₂ : ∀ t ∈ Q, t ∉ (center Q).map Q.subtype → orderOf t = 2 →
      (¬ ∃ g : G, g⁻¹ * z * g = t) →
        z ∈ CFSG.inSubgroup (CFSG.pCore 2) (centralizer ({t} : Set G)) := fun t htQ htZ ht2 hnf =>
    ((hinv t htQ htZ ht2).2.2.2.2 hnf).2.2.2
      (involution_centralizer_core_and_components hchar ht2).1
  refine ⟨hidx2, fun t htQ htZ ht2 => ?_, fun hset t htQ ht2 => ?_⟩
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hinv t htQ htZ ht2
    exact ⟨h1, h2, h3, h4, fun hnf => ⟨(h5 hnf).1, (h5 hnf).2.1, hO₂ t htQ htZ ht2 hnf⟩⟩
  · by_cases htZ : t ∈ (center Q).map Q.subtype
    · rw [huniq t htZ ht2, ← hM, ← hQ]
      exact map_subtype_le _ hzZ
    · refine hO₂ t htQ htZ ht2 fun ⟨g, hg⟩ => htZ ?_
      have h1 : t ∈ {w | ∃ g : G, g⁻¹ * z * g = w} ∩ (Q : Set G) := ⟨⟨g, hg⟩, htQ⟩
      rw [hset, Set.mem_singleton_iff] at h1
      rw [h1]
      exact hzZ

end SteinbergCH

open SteinbergCH

theorem gf2_center_four_symplectic_embedding_and_fusion
    {G : Type*} [Group G] [Finite G]
    (hchar : IsCharacteristicPType G 2) (he : 3 ≤ CFSG.twoLocalOddRank G) {M B : Subgroup G}
    (hM : GLAIsMaxTwoLocal M) (hsym : GLASymplecticType (pCoreOf 2 M)) (hB : GLAIsBmax 3 B)
    (hBM : B ≤ M) {Q : Subgroup G} (hQ : Q = CFSG.inSubgroup (CFSG.pCore 2) M)
    (hnex : ¬ IsExtraspecialPGroup 2 Q) (hexp : ∀ x ∈ Q, x ^ 4 = 1) :
    IsCyclic (center Q) ∧ Nat.card (center Q) = 4 ∧
    ∃ z ∈ (center Q).map Q.subtype, orderOf z = 2 ∧
      (∀ y ∈ (center Q).map Q.subtype, orderOf y = 2 → y = z) ∧
      ⁅Q, Q⁆ = zpowers z ∧ (frattini Q).map Q.subtype = zpowers z ∧
      (∃ (_ : CFSG.IsElementaryAbelian 2 (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))),
        (∃! v : ℕ, 1 ≤ v ∧ Module.finrank (ZMod 2)
          (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) = 2 * v) ∧
        ∃ b : LinearMap.BilinForm (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))),
          (∀ x y : CFSG.pCore 2 M, (((⁅x, y⁆ : CFSG.pCore 2 M) : M) : G) =
            z ^ (b (Additive.ofMul (x : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))
              (Additive.ofMul (y : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))).val) ∧
          (∀ b' : LinearMap.BilinForm (ZMod 2)
              (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))),
            (∀ x y : CFSG.pCore 2 M, (((⁅x, y⁆ : CFSG.pCore 2 M) : M) : G) =
              z ^ (b' (Additive.ofMul (x : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))
                (Additive.ofMul (y : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))).val) →
            b' = b) ∧
          b.IsAlt ∧ b.Nondegenerate ∧
          ∃ ρ : M →* LinearMap.GeneralLinearGroup (ZMod 2)
              (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))),
            (∀ (h : M) (x y : CFSG.pCore 2 M), (y : M) = h * x * h⁻¹ →
              ((ρ h : LinearMap.GeneralLinearGroup (ZMod 2)
                  (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))) :
                Module.End (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))))
                  (Additive.ofMul (x : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) =
                Additive.ofMul (y : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) ∧
            ρ.ker = CFSG.pCore 2 M ∧ (∀ h, ρ h ∈ bilinIsometryGroup b) ∧
            (∃ ι : M ⧸ CFSG.pCore 2 M →* bilinIsometryGroup b, Function.Injective ι ∧
              ∀ h : M, ((ι (h : M ⧸ CFSG.pCore 2 M) : bilinIsometryGroup b) :
                LinearMap.GeneralLinearGroup (ZMod 2)
                  (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))) = ρ h) ∧
            ∀ x (hx : x ∈ B), ρ ⟨x, hBM hx⟩ = 1 → x = 1) ∧
      M = centralizer {z} ∧ (∀ S : Subgroup G, IsSylowOf 2 S M → IsSylowOf 2 S ⊤) ∧
      (∀ L : Subgroup G, L ≤ Q → L.relIndex Q = 2 → ∀ x ∈ centralizer (L : Set G),
        orderOf x = 2 → x ∈ L) ∧
      (∀ t ∈ Q, t ∉ (center Q).map Q.subtype → orderOf t = 2 →
        (Q ⊓ centralizer ({t} : Set G)).relIndex Q = 2 ∧
        (center ↥(Q ⊓ centralizer ({t} : Set G))).map (Q ⊓ centralizer ({t} : Set G)).subtype =
          (center Q).map Q.subtype ⊔ zpowers t ∧
        (∃ q ∈ Q, q * t * q⁻¹ = t * z) ∧
        ((∃ g : G, g⁻¹ * z * g = t) ↔
          ∃ g : G, g ∉ M ∧ Q ⊓ centralizer ({t} : Set G) ≤ conjugate M g) ∧
        ((¬ ∃ g : G, g⁻¹ * z * g = t) →
          {w | ∃ g : G, g⁻¹ * z * g = w} ∩
              (centralizer ((Q ⊓ centralizer ({t} : Set G) : Subgroup G) : Set G) : Set G) =
            {z} ∧
          normalizer ((Q ⊓ centralizer ({t} : Set G) : Subgroup G) : Set G) ≤ M ∧
          z ∈ CFSG.inSubgroup (CFSG.pCore 2) (centralizer ({t} : Set G)))) ∧
      ({w | ∃ g : G, g⁻¹ * z * g = w} ∩ (Q : Set G) = {z} →
        ∀ t ∈ Q, orderOf t = 2 →
          z ∈ CFSG.inSubgroup (CFSG.pCore 2) (centralizer ({t} : Set G))) := by
  classical
  have hcharM : IsCharacteristicP 2 M := hchar M hM.1
  obtain ⟨⟨z, hzZ, hzord, huniq, hMC, -, -, hSyl⟩, -⟩ :=
    gf2_witness_centralizer_and_rank hchar hM hsym hB hBM hQ rfl
  obtain ⟨⟨D, hD⟩, hBK⟩ := gf2_critical_center_and_exponent_four_reduction hchar he hM hsym hB hBM
    hQ hzZ hzord rfl
  obtain ⟨-, -, hZ₀cyc, -, -, -, -, -, -, -, -, -, -, -, hcase⟩ := hBK D hD _ rfl _ rfl
  have hnotB : ¬ (8 ≤ Nat.card ((center D).map D.subtype) ∧ ∃ x : Q, 8 ≤ orderOf x) := by
    rintro ⟨-, x, hx⟩
    have h1 : x ^ 4 = 1 := Subtype.ext (by rw [SubgroupClass.coe_pow]; exact hexp x x.2)
    have h2 := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one h1)
    omega
  obtain ⟨-, -, hZ₀, hZ₀card, -, -, -, hQ', hΦ, -, hVel, -, -, -, -⟩ :=
    (hcase hnex).elim (fun h => h.1) fun h => absurd h.1 hnotB
  rw [hZ₀] at hZ₀cyc hZ₀card
  have hQ'G : ⁅Q, Q⁆ = zpowers z := by rw [← map_subtype_commutator]; exact hQ'
  have hBodd : Odd (Nat.card B) := by
    rw [hB.2.1]
    exact Odd.pow (by decide)
  have hSylM : ∃ S : Sylow 2 G, (S : Subgroup G) ≤ M := by
    obtain ⟨T₀⟩ : Nonempty (Sylow 2 M) := inferInstance
    obtain ⟨-, hT2, hidx⟩ := CFSG.ABGLocalTools.isSylowOf_iff.mp (hSyl _ ⟨T₀, rfl⟩).1
    rw [relIndex_top_right] at hidx
    exact ⟨hT2.toSylow hidx, by rw [IsPGroup.toSylow_coe]; exact map_subtype_le _⟩
  obtain ⟨hidx2, hnoncentral, hwc⟩ :=
    core_fusion_package hchar hzord hMC hcharM hQ hΦ hQ'G hZ₀cyc hSylM hzZ huniq
  exact ⟨hZ₀cyc, hZ₀card, z, hzZ, hzord, huniq, hQ'G, hΦ,
    core_symplectic_transport hBM hcharM hBodd hQ hZ₀cyc hVel hzZ hzord hQ'G, hMC,
    fun S hS => (hSyl S hS).1, hidx2, hnoncentral, hwc⟩

end CFSG.LocalAnalysis.GorensteinLyons
