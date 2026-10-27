module

public import CFSG.Goldschmidt.BasicG
public import CFSG.Goldschmidt.Steps.G310TransQuot
import CFSG.GroupTheory.QuasiDihedralFusion.Basic

public section

namespace CFSG.Goldschmidt.G310

open CFSG.Open

variable {G : Type*} [Group G]

theorem le_normalizer_oddCoreOf (H : Subgroup G) :
    H ≤ Subgroup.normalizer ((oddCoreOf H : Subgroup G) : Set G) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨o, ho, rfl⟩
    exact ⟨⟨h, hh⟩ * o * ⟨h, hh⟩⁻¹, (goldschmidtOddCore_normal H).conj_mem o ho ⟨h, hh⟩, rfl⟩
  · rintro ⟨o, ho, hoy⟩
    have hoy : (o : G) = h * y * h⁻¹ := hoy
    have hyH : y ∈ H := by
      have e : y = h⁻¹ * (o : G) * h := by rw [hoy]; group
      rw [e]
      exact H.mul_mem (H.mul_mem (H.inv_mem hh) o.2) hh
    refine ⟨⟨y, hyH⟩, ?_, rfl⟩
    have := (goldschmidtOddCore_normal H).conj_mem o ho ⟨h, hh⟩⁻¹
    have e : (⟨h, hh⟩ : H)⁻¹ * o * (⟨h, hh⟩⁻¹)⁻¹ = ⟨y, hyH⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
      rw [hoy]
      group
    rwa [e] at this

theorem oddCoreOf_le (H : Subgroup G) : oddCoreOf H ≤ H := Subgroup.map_subtype_le _

theorem le_oddCoreOf_of_normalizer {K X : Subgroup G} (hKX : K ≤ X)
    (hXK : X ≤ Subgroup.normalizer (K : Set G)) (hK : ¬ 2 ∣ Nat.card K) : K ≤ oddCoreOf X := by
  have hn : (K.subgroupOf X).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKX).mpr hXK
  have hodd : Odd (Nat.card (K.subgroupOf X)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKX).toEquiv]
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hK)
  have hle : K.subgroupOf X ≤ goldschmidtOddCore X := le_sSup ⟨hn, hodd⟩
  intro k hk
  exact ⟨⟨k, hKX hk⟩, hle hk, rfl⟩

variable [Finite G]

theorem not_two_dvd_card_oddCoreOf (H : Subgroup G) : ¬ 2 ∣ Nat.card (oddCoreOf H) := by
  rw [oddCoreOf, Subgroup.card_map_of_injective H.subtype_injective]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [goldschmidtOddCore_eq_pPrimeCore]
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp CFSG.pPrimeCore_coprime_card

theorem not_two_dvd_card_sup {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {P K : Subgroup G}
    (hP : IsPGroup p P) (hPK : P ≤ Subgroup.normalizer (K : Set G)) (hK : ¬ 2 ∣ Nat.card K) :
    ¬ 2 ∣ Nat.card (P ⊔ K : Subgroup G) := by
  set Y := Subgroup.normalizer (K : Set G) with hY
  have hKY : K ≤ Y := Subgroup.le_normalizer
  have hsupY : P ⊔ K ≤ Y := sup_le hPK hKY
  have : (K.subgroupOf Y).Normal := Subgroup.normal_in_normalizer
  have hK' : ¬ 2 ∣ Nat.card (K.subgroupOf Y) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKY).toEquiv]
  have h := not_two_dvd_card_comap (X := Y) hK' hp2 hp
    (hP.comap_subtype.map (QuotientGroup.mk' (K.subgroupOf Y)))
  rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h
  have e : Subgroup.comap Y.subtype P ⊔ K.subgroupOf Y = (P ⊔ K).subgroupOf Y :=
    (Subgroup.subgroupOf_sup hPK hKY).symm
  rw [e, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsupY).toEquiv] at h
  exact h

omit [Finite G] in
theorem exists_mul_of_mem_sup {H K : Subgroup G} (hH : H ≤ Subgroup.normalizer (K : Set G))
    {x : G} (hx : x ∈ H ⊔ K) : ∃ y ∈ H, ∃ z ∈ K, y * z = x := by
  set L := H ⊔ K with hL
  have : (K.subgroupOf L).Normal := Subgroup.normal_subgroupOf_sup_of_le_normalizer hH
  have hx' : (⟨x, hx⟩ : L) ∈ H.subgroupOf L ⊔ K.subgroupOf L := by
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
    exact Subgroup.mem_top _
  obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_right.mp hx'
  exact ⟨y, hy, z, hz, congrArg Subtype.val hyz⟩

theorem exists_mem_centralizer_of_coset {A P K : Subgroup G} (hA : IsPGroup 2 A)
    (hAP : A ≤ Subgroup.normalizer (P : Set G)) (hAK : A ≤ Subgroup.normalizer (K : Set G))
    (hPK : ¬ 2 ∣ Nat.card (P ⊓ K : Subgroup G)) {m x₀ : G}
    (hm : m ∈ Subgroup.centralizer (A : Set G)) (hx₀ : x₀ ∈ P) (hx₀m : x₀⁻¹ * m ∈ K) :
    ∃ x ∈ P ⊓ Subgroup.centralizer (A : Set G), x⁻¹ * m ∈ K := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let F := {x : P // ((x : P) : G)⁻¹ * m ∈ K}
  have hcomm : ∀ a ∈ A, a * m = m * a := fun a ha =>
    (Subgroup.mem_centralizer_iff.mp hm a ha)
  let act : MulAction A F :=
    { smul := fun a x => ⟨⟨(a : G) * x.1 * (a : G)⁻¹,
        conj_mem_of_mem_normalizer (hAP a.2) x.1.2⟩, by
          have h1 := conj_mem_of_mem_normalizer (hAK a.2) x.2
          have e : ((a : G) * ((x.1 : P) : G) * (a : G)⁻¹)⁻¹ * m =
              (a : G) * (((x.1 : P) : G)⁻¹ * m) * (a : G)⁻¹ := by
            have hc := hcomm a a.2
            calc ((a : G) * ((x.1 : P) : G) * (a : G)⁻¹)⁻¹ * m
                = (a : G) * ((x.1 : P) : G)⁻¹ * ((a : G)⁻¹ * m) := by group
              _ = (a : G) * ((x.1 : P) : G)⁻¹ * (m * (a : G)⁻¹) := by
                  rw [show (a : G)⁻¹ * m = m * (a : G)⁻¹ by
                    calc (a : G)⁻¹ * m = (a : G)⁻¹ * (m * a) * (a : G)⁻¹ := by group
                      _ = (a : G)⁻¹ * (a * m) * (a : G)⁻¹ := by rw [hc]
                      _ = m * (a : G)⁻¹ := by group]
              _ = (a : G) * (((x.1 : P) : G)⁻¹ * m) * (a : G)⁻¹ := by group
          rw [e]
          exact h1⟩
      one_smul := fun x => by
        apply Subtype.ext; apply Subtype.ext
        change (1 : G) * _ * (1 : G)⁻¹ = _
        group
      mul_smul := fun a b x => by
        apply Subtype.ext; apply Subtype.ext
        change ((a : G) * b) * _ * ((a : G) * b)⁻¹ = (a : G) * ((b : G) * _ * (b : G)⁻¹) * (a : G)⁻¹
        group }
  have hF : Nat.card F = Nat.card (P ⊓ K : Subgroup G) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨x₀⁻¹ * ((x.1 : P) : G), P.mul_mem (P.inv_mem hx₀) x.1.2, by
          have := K.mul_mem hx₀m (K.inv_mem x.2)
          simpa [mul_assoc] using this⟩
        invFun := fun y => ⟨⟨x₀ * y, P.mul_mem hx₀ y.2.1⟩, by
          have := K.mul_mem (K.inv_mem y.2.2) hx₀m
          simpa [mul_assoc] using this⟩
        left_inv := fun x => by
          apply Subtype.ext; apply Subtype.ext
          change x₀ * (x₀⁻¹ * _) = _
          group
        right_inv := fun y => by
          apply Subtype.ext
          change x₀⁻¹ * (x₀ * _) = _
          group }
  have hFodd : ¬ 2 ∣ Nat.card F := by rw [hF]; exact hPK
  have : Finite F := inferInstance
  obtain ⟨x, hx⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card F hFodd
  refine ⟨x.1, ⟨x.1.2, Subgroup.mem_centralizer_iff.mpr fun a ha => ?_⟩, x.2⟩
  have h := congrArg (fun y : F => ((y.1 : P) : G)) (MulAction.mem_fixedPoints.mp hx ⟨a, ha⟩)
  change a * ((x.1 : P) : G) * a⁻¹ = x.1 at h
  calc a * ((x.1 : P) : G) = a * ((x.1 : P) : G) * a⁻¹ * a := by group
    _ = (x.1 : G) * a := by rw [h]

theorem sup_oddCoreOf_inf_centralizer_le {H A P : Subgroup G} (hAH : A ≤ H) (hA : IsPGroup 2 A)
    {p : ℕ} (hP : P ∈ sigN H A p) :
    (P ⊔ oddCoreOf H) ⊓ Subgroup.centralizer (A : Set G) ≤
      oddCoreOf (H ⊓ Subgroup.centralizer (A : Set G)) := by
  obtain ⟨hPH, hPp, hAP, hPC⟩ := hP
  set O := oddCoreOf H with hO
  have hPO : P ≤ Subgroup.normalizer (O : Set G) := hPH.trans (le_normalizer_oddCoreOf H)
  have hAO : A ≤ Subgroup.normalizer (O : Set G) := hAH.trans (le_normalizer_oddCoreOf H)
  have hOodd := not_two_dvd_card_oddCoreOf H
  have hPOodd : ¬ 2 ∣ Nat.card (P ⊓ O : Subgroup G) := fun h =>
    hOodd (h.trans (Subgroup.card_dvd_of_le inf_le_right))
  have hOC : O ⊓ Subgroup.centralizer (A : Set G) ≤
      oddCoreOf (H ⊓ Subgroup.centralizer (A : Set G)) := by
    refine le_oddCoreOf_of_normalizer (inf_le_inf_right _ (oddCoreOf_le H)) ?_ ?_
    · exact le_normalizer_inf (inf_le_left.trans (le_normalizer_oddCoreOf H))
        (inf_le_right.trans (Subgroup.le_normalizer))
    · exact fun h => hOodd (h.trans (Subgroup.card_dvd_of_le inf_le_left))
  rintro m ⟨hmM, hmC⟩
  obtain ⟨x₀, hx₀, o, ho, hx₀o⟩ := exists_mul_of_mem_sup hPO hmM
  have hx₀m : x₀⁻¹ * m ∈ O := by rw [← hx₀o]; simpa using ho
  obtain ⟨x, hx, hxm⟩ := exists_mem_centralizer_of_coset hA hAP hAO hPOodd hmC hx₀ hx₀m
  have hxm' : x⁻¹ * m ∈ O ⊓ Subgroup.centralizer (A : Set G) :=
    ⟨hxm, Subgroup.mul_mem _ (Subgroup.inv_mem _ hx.2) hmC⟩
  have : m = x * (x⁻¹ * m) := by group
  rw [this]
  exact Subgroup.mul_mem _ (hPC hx) (hOC hxm')

theorem fusionIsSylowIn_of_maximal_sigN {H A P : Subgroup G} (hAH : A ≤ H) (hA : IsPGroup 2 A)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hP : Maximal (· ∈ sigN H A p) P) :
    fusionIsSylowIn p P (P ⊔ oddCoreOf H) ∧
      fusionIsSylowIn p (P ⊓ oddCoreOf H) (oddCoreOf H) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hPH, hPp, hAP, hPC⟩ := hP.prop
  set O := oddCoreOf H with hO
  set M := P ⊔ O with hMdef
  have hPO : P ≤ Subgroup.normalizer (O : Set G) := hPH.trans (le_normalizer_oddCoreOf H)
  have hAO : A ≤ Subgroup.normalizer (O : Set G) := hAH.trans (le_normalizer_oddCoreOf H)
  have hModd : ¬ 2 ∣ Nat.card M :=
    not_two_dvd_card_sup hp hp2 hPp hPO (not_two_dvd_card_oddCoreOf H)
  have hAM : A ≤ Subgroup.normalizer (M : Set G) := le_normalizer_sup hAP hAO
  obtain ⟨S, hS, hPS, hAS⟩ := exists_invariant_sylow_containing Nat.prime_two hp hA hModd hAM
    le_sup_left hPp hAP
  have hMH : M ≤ H := sup_le hPH (oddCoreOf_le H)
  have hSsig : S ∈ sigN H A p :=
    ⟨hS.1.trans hMH, hS.2.1, hAS, (inf_le_inf_right _ hS.1).trans
      (sup_oddCoreOf_inf_centralizer_le hAH hA hP.prop)⟩
  have hSP : S = P := le_antisymm (hP.2 hSsig hPS) hPS
  rw [hSP] at hS
  refine ⟨hS, ?_⟩
  obtain ⟨T, hT⟩ := exists_sylow_of_fusionIsSylowIn hS
  have hOM : O ≤ M := le_sup_right
  have hOn : (O.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hOM).mpr (sup_le hPO Subgroup.le_normalizer)
  have hp' : IsPGroup p ((T : Subgroup M).subgroupOf (O.subgroupOf M)) :=
    T.isPGroup'.comap_subtype
  have hidx : ¬ p ∣ ((T : Subgroup M).subgroupOf (O.subgroupOf M)).index := by
    intro hdvd
    exact T.not_dvd_index (dvd_trans hdvd
      (CFSG.QuasiDihedralFusion.relIndex_dvd_index_of_normal_right (T : Subgroup M)
        (O.subgroupOf M)))
  let T' : Sylow p (O.subgroupOf M) := hp'.toSylow hidx
  have hT' : (T' : Subgroup (O.subgroupOf M)) = (T : Subgroup M).subgroupOf (O.subgroupOf M) :=
    IsPGroup.toSylow_coe _ _
  let e : O.subgroupOf M ≃* O := Subgroup.subgroupOfEquivOfLe hOM
  let T'' : Sylow p O := T'.mapSurjective (f := e.toMonoidHom) e.surjective
  have hT'' : (T'' : Subgroup O) = (T' : Subgroup (O.subgroupOf M)).map e.toMonoidHom :=
    Sylow.coe_mapSurjective _ _
  have hmap : ((T'' : Subgroup O).map O.subtype) = P ⊓ O := by
    rw [hT'', hT']
    ext x
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      have h1 : ((y : M) : G) ∈ (T : Subgroup M).map M.subtype := ⟨y, hy, rfl⟩
      rw [hT] at h1
      exact ⟨h1, y.2⟩
    · rintro ⟨hxP, hxO⟩
      refine ⟨⟨x, hxO⟩, ⟨⟨⟨x, hOM hxO⟩, hxO⟩, ?_, rfl⟩, rfl⟩
      change (⟨x, hOM hxO⟩ : M) ∈ (T : Subgroup M)
      have h1 : x ∈ (T : Subgroup M).map M.subtype := by rw [hT]; exact hxP
      obtain ⟨z, hz, hzx⟩ := h1
      rwa [show z = ⟨x, hOM hxO⟩ from Subtype.ext hzx] at hz
  rw [← hmap]
  exact fusionIsSylowIn_map T''

end CFSG.Goldschmidt.G310
