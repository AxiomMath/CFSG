module

public import CFSG.CharacterTheory.Semidihedral.AllPrimeLayerFacts
public import CFSG.CharacterTheory.Semidihedral.SmallerRecognitionOddCoreControl
public import CFSG.GroupTheory.QuasiDihedralFusion.QGroup
public import CFSG.GroupTheory.PCore.CommutingBalance

public noncomputable section

namespace CFSG.Semidihedral.AllPrime

open CFSG.Open CFSG.Semidihedral CFSG.ABGTheoremB CFSG.QuasiDihedralFusion
open CFSG.Semidihedral.SmallerRecognitionOddCoreControl

section Wreath

open CFSG.Wreathed (Wreath)

private theorem wreath_half_involution (k : ℕ) :
    orderOf (Wreathed.element (2 ^ (k + 1)) ((2 ^ k : ℕ) : ZMod (2 ^ (k + 1))) 0 0) = 2 ∧
      Wreathed.element (2 ^ (k + 1)) 0 0 1 *
          Wreathed.element (2 ^ (k + 1)) ((2 ^ k : ℕ) : ZMod (2 ^ (k + 1))) 0 0 *
          (Wreathed.element (2 ^ (k + 1)) 0 0 1)⁻¹ ≠
        Wreathed.element (2 ^ (k + 1)) ((2 ^ k : ℕ) : ZMod (2 ^ (k + 1))) 0 0 := by
  refine ⟨(Wreathed.element_base_involution_iff k _ _).mpr (Or.inr (Or.inl ⟨rfl, rfl⟩)), ?_⟩
  rw [Wreathed.conjugate_base_by_swap]
  intro h
  rw [Wreathed.element_eq_iff] at h
  exact Wreathed.half_residue_ne_zero k h.1.symm

private theorem wreath_not_embed_semidihedral {n k : ℕ} (hn : 4 ≤ n) (hk : 1 ≤ k)
    (ι : Wreath (2 ^ (k + 1)) →* SemidihedralGroup n) (hι : Function.Injective ι) : False := by
  have := presentation_finite n (by omega)
  obtain ⟨hx2, hxw⟩ := wreath_half_involution k
  set x := Wreathed.element (2 ^ (k + 1)) ((2 ^ k : ℕ) : ZMod (2 ^ (k + 1))) 0 0 with hx
  set y := Wreathed.element (2 ^ (k + 1)) 1 0 0 with hy
  set w := Wreathed.element (2 ^ (k + 1)) 0 0 1 with hw
  have hxy : x * y = y * x := by
    rw [hx, hy, Wreathed.element_base_mul, Wreathed.element_base_mul, Wreathed.element_eq_iff]
    exact ⟨add_comm _ _, rfl, rfl⟩
  have hy2 : y ^ 2 ≠ 1 := by
    rw [hy, Wreathed.element_base_pow]
    intro h2
    rw [Wreathed.element_base_eq_one_iff] at h2
    have h2' : ((2 : ℕ) : ZMod (2 ^ (k + 1))) = 0 := by simpa [nsmul_eq_mul] using h2.1
    rw [ZMod.natCast_eq_zero_iff] at h2'
    have hle := Nat.le_of_dvd (by norm_num) h2'
    have h4 : 2 ^ 2 ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hX2 : orderOf (ι x) = 2 := by rw [orderOf_injective ι hι, hx2]
  have hXz : ι x ∉ Subgroup.zpowers (z n) := by
    intro h
    rcases (KleinFourOddKernel.mem_zpowers_involution _ _ (orderOf_z n (by omega))).mp h with
      h1 | h1
    · rw [h1, orderOf_one] at hX2
      omega
    · apply hxw
      apply hι
      rw [map_mul, map_mul, map_inv, h1,
        Subgroup.mem_center_iff.mp (z_mem_center n hn) (ι w), mul_inv_cancel_right]
  obtain ⟨h1, -, -⟩ := Local.semidihedral_four_subgroup_centralizers n hn
    (MulEquiv.refl (SemidihedralGroup n))
  have hz : (MulEquiv.refl (SemidihedralGroup n)) (r n) ^ (2 ^ (n - 1) / 2) = z n := by
    rw [MulEquiv.refl_apply, two_pow_div_two hn]
    rfl
  rw [hz] at h1
  obtain ⟨hC, hK⟩ := h1 (ι x) hX2 hXz
  have hYC : ι y ∈ Subgroup.centralizer ({ι x} : Set (SemidihedralGroup n)) := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hxy]
  rw [hC] at hYC
  have hYsq := congrArg Subtype.val (IsKleinFour.mul_self (⟨ι y, hYC⟩ :
    Subgroup.closure ({z n, ι x} : Set (SemidihedralGroup n))))
  apply hy2
  apply hι
  rw [map_pow, map_one, pow_two]
  exact hYsq

private theorem wreath_central_mem_kleinFour (k : ℕ) (V : Subgroup (Wreath (2 ^ (k + 1))))
    (hV : IsKleinFour V) :
    Wreathed.element (2 ^ (k + 1)) ((2 ^ k : ℕ) : ZMod (2 ^ (k + 1)))
      ((2 ^ k : ℕ) : ZMod (2 ^ (k + 1))) 0 ∈ V := by
  have hh : ((2 ^ k : ℕ) : ZMod (2 ^ (k + 1))) ≠ 0 := Wreathed.half_residue_ne_zero k
  have hsq : ∀ a ∈ V, a * a = 1 := fun a ha =>
    congrArg Subtype.val (IsKleinFour.mul_self (⟨a, ha⟩ : V))
  have hcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val ((IsKleinFour.isMulCommutative (G := V)).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hnot : ∀ v ∈ V, ∃ u ∈ V, u ≠ 1 ∧ u ≠ v := by
    intro v _
    by_contra hcon
    push Not at hcon
    have hsub : (V : Set (Wreath (2 ^ (k + 1)))) ⊆ {1, v} := fun u hu => by
      by_cases hu1 : u = 1
      · exact Or.inl hu1
      · exact Or.inr (hcon u hu hu1)
    have hcard := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe, IsKleinFour.card_four] at hcard
    have h2 := Set.ncard_insert_le (1 : Wreath (2 ^ (k + 1))) {v}
    rw [Set.ncard_singleton] at h2
    omega
  have hinv : ∀ a ∈ V, a ≠ 1 → orderOf a = 2 := fun a ha ha1 =>
    orderOf_eq_prime (by rw [pow_two]; exact hsq a ha) ha1
  have hkey : ∀ a b a' b' : ZMod (2 ^ (k + 1)),
      ((a = (2 ^ k : ℕ) ∧ b = 0) ∨ (a = 0 ∧ b = (2 ^ k : ℕ))) →
      ((a' = (2 ^ k : ℕ) ∧ b' = 0) ∨ (a' = 0 ∧ b' = (2 ^ k : ℕ))) → ¬ (a = a' ∧ b = b') →
        a + a' = (2 ^ k : ℕ) ∧ b + b' = (2 ^ k : ℕ) := by
    rintro a b a' b' (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) hne
    · exact absurd ⟨rfl, rfl⟩ hne
    · exact ⟨add_zero _, zero_add _⟩
    · exact ⟨zero_add _, add_zero _⟩
    · exact absurd ⟨rfl, rfl⟩ hne
  obtain ⟨a, b, hw, hw1⟩ : ∃ a b : ZMod (2 ^ (k + 1)), Wreathed.element _ a b 0 ∈ V ∧
      Wreathed.element _ a b 0 ≠ 1 := by
    obtain ⟨v₁, hv₁, hv₁1, -⟩ := hnot 1 (Subgroup.one_mem _)
    obtain ⟨v₂, hv₂, hv₂1, hv₂₁⟩ := hnot v₁ hv₁
    obtain ⟨⟨a₁, b₁, e₁⟩, rfl⟩ := (Wreathed.coordinateEquiv (2 ^ (k + 1))).symm.surjective v₁
    obtain ⟨⟨a₂, b₂, e₂⟩, rfl⟩ := (Wreathed.coordinateEquiv (2 ^ (k + 1))).symm.surjective v₂
    change Wreathed.element _ a₁ b₁ e₁ ∈ V at hv₁
    change Wreathed.element _ a₂ b₂ e₂ ∈ V at hv₂
    change Wreathed.element _ a₁ b₁ e₁ ≠ 1 at hv₁1
    change Wreathed.element _ a₂ b₂ e₂ ≠ 1 at hv₂1
    change Wreathed.element _ a₂ b₂ e₂ ≠ Wreathed.element _ a₁ b₁ e₁ at hv₂₁
    rcases Wreathed.swap_exponent_cases e₁ with rfl | rfl
    · exact ⟨a₁, b₁, hv₁, hv₁1⟩
    rcases Wreathed.swap_exponent_cases e₂ with rfl | rfl
    · exact ⟨a₂, b₂, hv₂, hv₂1⟩
    refine ⟨a₁ + b₂, b₁ + a₂, ?_, ?_⟩
    · have hmem := V.mul_mem hv₁ hv₂
      rwa [Wreathed.element_swap_mul, show (1 + 1 : ZMod 2) = 0 by decide] at hmem
    · intro h1
      apply hv₂₁
      have hprod : Wreathed.element _ a₁ b₁ 1 * Wreathed.element (2 ^ (k + 1)) a₂ b₂ 1 = 1 := by
        rw [Wreathed.element_swap_mul, show (1 + 1 : ZMod 2) = 0 by decide]
        exact h1
      calc Wreathed.element _ a₂ b₂ 1 = Wreathed.element (2 ^ (k + 1)) a₁ b₁ 1 *
            (Wreathed.element _ a₁ b₁ 1 * Wreathed.element (2 ^ (k + 1)) a₂ b₂ 1) := by
            rw [← mul_assoc, hsq _ hv₁, one_mul]
        _ = Wreathed.element _ a₁ b₁ 1 := by rw [hprod, mul_one]
  rcases (Wreathed.element_base_involution_iff k a b).mp (hinv _ hw hw1) with
    ⟨rfl, rfl⟩ | hab | hab
  · exact hw
  all_goals
    have hab₀ : (a = (2 ^ k : ℕ) ∧ b = 0) ∨ (a = 0 ∧ b = (2 ^ k : ℕ)) := by tauto
    have hab' : a ≠ b := by
      rcases hab₀ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hh
      · exact fun h0 => hh h0.symm
    have hVbase : ∀ a' b' e', Wreathed.element (2 ^ (k + 1)) a' b' e' ∈ V → e' = 0 := by
      intro a' b' e' hv
      rcases Wreathed.swap_exponent_cases e' with rfl | rfl
      · rfl
      · exfalso
        have hc := hcomm _ hv _ hw
        have hconj : Wreathed.element _ a' b' 1 * Wreathed.element (2 ^ (k + 1)) a b 0 *
            (Wreathed.element _ a' b' 1)⁻¹ = Wreathed.element (2 ^ (k + 1)) a b 0 := by
          rw [hc, mul_inv_cancel_right]
        rw [Wreathed.conjugate_base_by_swap, Wreathed.element_eq_iff] at hconj
        exact hab' hconj.1.symm
    obtain ⟨v, hv, hv1, hvw⟩ := hnot _ hw
    obtain ⟨⟨a', b', e'⟩, rfl⟩ := (Wreathed.coordinateEquiv (2 ^ (k + 1))).symm.surjective v
    change Wreathed.element _ a' b' e' ∈ V at hv
    change Wreathed.element _ a' b' e' ≠ 1 at hv1
    change Wreathed.element _ a' b' e' ≠ Wreathed.element (2 ^ (k + 1)) a b 0 at hvw
    obtain rfl := hVbase a' b' e' hv
    rcases (Wreathed.element_base_involution_iff k a' b').mp (hinv _ hv hv1) with
      ⟨rfl, rfl⟩ | hab'' | hab''
    · exact hv
    all_goals
      have hab₁ : (a' = (2 ^ k : ℕ) ∧ b' = 0) ∨ (a' = 0 ∧ b' = (2 ^ k : ℕ)) := by tauto
      have hne : ¬ (a = a' ∧ b = b') := by
        rintro ⟨rfl, rfl⟩
        exact hvw rfl
      obtain ⟨h1, h2⟩ := hkey a b a' b' hab₀ hab₁ hne
      have hmem := V.mul_mem hw hv
      rwa [Wreathed.element_base_mul, h1, h2] at hmem

end Wreath

section WorkingI

variable {G : Type} [Group G]

private theorem centralizer_singleton_eq_inf_subgroupOf (H : Subgroup G) (t : H) :
    Subgroup.centralizer ({t} : Set H) =
      (H ⊓ Subgroup.centralizer ({(t : G)} : Set G)).subgroupOf H := by
  ext c
  simp only [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
    SetLike.coe_mem, true_and, Subtype.ext_iff, Subgroup.coe_mul]

private theorem map_pPrimeCore_centralizer_eq_oddCoreIn (H : Subgroup G) (t : H) :
    ((CFSG.pPrimeCore 2 (Subgroup.centralizer ({t} : Set H))).map
      (Subgroup.centralizer ({t} : Set H)).subtype).map H.subtype =
        oddCoreIn (H ⊓ Subgroup.centralizer ({(t : G)} : Set G)) := by
  rw [centralizer_singleton_eq_inf_subgroupOf, oddCoreIn,
    QuaternionFocalFactorization.oddCore_eq_twoPrimeCore]
  exact CFSG.pPrimeCore_map_subgroupOf 2 _ H inf_le_left

private theorem not_hasWreathedSylow [Finite G] {n : ℕ} (hn : 4 ≤ n) (S : Sylow 2 G)
    (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (H : Subgroup G) {h : ℕ}
    (hW : HasWreathedSylow H h) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hh2, hP⟩ := hW
  obtain ⟨P⟩ : Nonempty (Sylow 2 H) := inferInstance
  obtain ⟨eP⟩ := hP P
  have hQ : IsPGroup 2 ((P : Subgroup H).map H.subtype) := P.isPGroup'.map H.subtype
  obtain ⟨S', hS'⟩ := hQ.exists_le_sylow
  let f' : SemidihedralGroup n ≃* (S' : Subgroup G) := fS.trans (Sylow.equiv S S')
  let φ : Wreathed.Wreath (2 ^ h) →* G :=
    (H.subtype.comp (P : Subgroup H).subtype).comp eP.symm.toMonoidHom
  have hφ : Function.Injective φ :=
    (H.subtype_injective.comp (P : Subgroup H).subtype_injective).comp eP.symm.injective
  have hφS : ∀ w, φ w ∈ (S' : Subgroup G) := fun w => hS' ⟨_, (eP.symm w).2, rfl⟩
  let ψ : Wreathed.Wreath (2 ^ h) →* SemidihedralGroup n :=
    f'.symm.toMonoidHom.comp (φ.codRestrict _ hφS)
  have hψ : Function.Injective ψ := by
    intro a b hab
    apply hφ
    have h1 := f'.symm.injective hab
    exact congrArg (fun u : (S' : Subgroup G) => (u : G)) h1
  obtain ⟨k, rfl⟩ : ∃ k, h = k + 1 := ⟨h - 1, by omega⟩
  exact wreath_not_embed_semidihedral hn (by omega) ψ hψ

private theorem qd_odd_core_commutator_control
    [Finite G] {n : ℕ} (hn : 4 ≤ n) (S : Sylow 2 G)
    (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (hsd : ProperSubgroupRegularity.SmallerSimpleRecognition G)
    (H : Subgroup G) (hH : H ≠ ⊤) (hQD : IsQDGroup H) (t : H) (ht : orderOf t = 2)
    (A : Subgroup H) (hA : IsPGroup 2 A) (hAC : A ≤ Subgroup.centralizer ({t} : Set H)) :
    ⁅A, (CFSG.pPrimeCore 2 (Subgroup.centralizer ({t} : Set H))).map
      (Subgroup.centralizer ({t} : Set H)).subtype⁆ ≤ CFSG.pPrimeCore 2 H := by
  obtain ⟨P⟩ : Nonempty (Sylow 2 H) := inferInstance
  obtain ⟨h, ⟨-, k, hk, hkP⟩ | hW⟩ := hQD.sylow
  · obtain ⟨fP⟩ := hkP P
    exact smaller_simple_recognition_produces_proper_subgroup_odd_core_control
      G hsd H hH hQD.noIndexTwo k hk P fP t ht A hAC hA
  · exact (not_hasWreathedSylow hn S fS H hW).elim

end WorkingI

theorem semidihedral_workingHypothesisI
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hrec : PerfectLayerNormalization.OriginalSmallerSimpleRecognition G)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G)) :
    WorkingHypothesisI G := by
  have hsd := PerfectLayerNormalization.original_smaller_simple_recognition_transport
    (Equiv.refl G) hrec
  intro H hH hQD y hyH hy T₁ hT₁H hT₁ hyT₁
  let t : H := ⟨y, hyH⟩
  have ht : orderOf t = 2 := by rw [Subgroup.orderOf_mk]; exact hy
  have hcomm : ∀ a ∈ T₁, a * y = y * a := by
    intro a ha
    exact congrArg Subtype.val
      ((IsKleinFour.isMulCommutative (G := T₁)).is_comm.comm ⟨a, ha⟩ ⟨y, hyT₁⟩)
  have hA : IsPGroup 2 (T₁.subgroupOf H) := by
    refine IsPGroup.of_card (n := 2) ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT₁H).toEquiv, IsKleinFour.card_four]
    norm_num
  have hAC : T₁.subgroupOf H ≤ Subgroup.centralizer ({t} : Set H) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext (hcomm a ha))
  have hcontrol := Subgroup.map_mono (f := H.subtype)
    (qd_odd_core_commutator_control hn S fS hsd H hH hQD t ht _ hA hAC)
  have hR : oddCoreIn H = (CFSG.pPrimeCore 2 H).map H.subtype := by
    rw [oddCoreIn, QuaternionFocalFactorization.oddCore_eq_twoPrimeCore]
  rw [hR]
  rwa [Subgroup.map_commutator, map_pPrimeCore_centralizer_eq_oddCoreIn,
    Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hT₁H] at hcontrol

section QGroup

private theorem kleinFour_mulAut_mul_self {V : Type*} [Group V] [Finite V] [IsKleinFour V]
    (φ : MulAut V) {x : V} (hx : x ≠ 1) (hφx : φ x = x) : φ * φ = 1 := by
  classical
  have := Fintype.ofFinite V
  ext v
  change φ (φ v) = v
  by_cases hv1 : v = 1
  · rw [hv1, map_one, map_one]
  by_cases hvx : v = x
  · rw [hvx, hφx, hφx]
  have hmem : φ v ∈ ({x * v, x, v, 1} : Finset V) := by
    rw [IsKleinFour.eq_finset_univ hx hv1 (Ne.symm hvx)]
    exact Finset.mem_univ _
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h | h
  · rw [h, map_mul, hφx, h, ← mul_assoc, IsKleinFour.mul_self, one_mul]
  · exact absurd (φ.injective (h.trans hφx.symm)) hvx
  · rw [h, h]
  · exact absurd (φ.injective (h.trans (map_one φ).symm)) hv1

private theorem exists_center_mem_of_embedding {H M : Type*} [Group H] [Group M]
    {S V : Subgroup H} (hVS : V ≤ S) (hV : IsKleinFour V) (ι : S →* M)
    (hι : Function.Injective ι) {zM : M} (hzM : zM ∈ Subgroup.center M) (hz1 : zM ≠ 1)
    (hKlein : ∀ W : Subgroup M, IsKleinFour W → zM ∈ W) :
    ∃ x ∈ V, x ∈ centerOf S ∧ x ≠ 1 := by
  have hW : IsKleinFour ((V.subgroupOf S).map ι) :=
    Local.isKleinFour_of_mulEquiv ((Subgroup.subgroupOfEquivOfLe hVS).symm.trans
      ((V.subgroupOf S).equivMapOfInjective ι hι))
  obtain ⟨v, hv, hvz⟩ := hKlein _ hW
  refine ⟨(v : H), hv, Subgroup.mem_inf.mpr ⟨v.2, ?_⟩, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have h := Subgroup.mem_center_iff.mp hzM (ι ⟨s, hs⟩)
    rw [← hvz, ← map_mul, ← map_mul] at h
    exact congrArg Subtype.val (hι h)
  · intro h1
    apply hz1
    rw [← hvz, show v = 1 from Subtype.ext h1, map_one]

end QGroup

theorem qgroup_no_three {G : Type} [Group G] [Finite G] (K : Subgroup G)
    (hK : IsQGroup K) (T₁ : Subgroup G) (hT₁K : T₁ ≤ K) (hT₁ : IsKleinFour T₁) :
    ¬ 3 ∣ automizerIndex (T₁.subgroupOf K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hV : IsKleinFour (T₁.subgroupOf K) :=
    Local.isKleinFour_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hT₁K).symm
  have hV2 : IsPGroup 2 (T₁.subgroupOf K) :=
    IsPGroup.of_card (n := 2) (by rw [IsKleinFour.card_four]; norm_num)
  obtain ⟨S, hVS⟩ := hV2.exists_le_sylow
  obtain ⟨x, hxV, hxS, hx1⟩ : ∃ x ∈ T₁.subgroupOf K, x ∈ centerOf (S : Subgroup K) ∧ x ≠ 1 := by
    obtain ⟨R, K', hdata⟩ := id hK
    obtain ⟨-, hι⟩ := hdata.quaternion
    rcases hι with ⟨k, hk, ι, hι, -⟩ | ⟨k, hk, ι, hι, -⟩
    · exact exists_center_mem_of_embedding hVS hV (ι.comp (Sylow.equiv S R).toMonoidHom)
        (hι.comp (Sylow.equiv S R).injective) (z_mem_center k hk) (z_ne_one k (by omega))
        (fun W hW => (sd_kleinFour_facts hk W).1)
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      refine exists_center_mem_of_embedding hVS hV (ι.comp (Sylow.equiv S R).toMonoidHom)
        (hι.comp (Sylow.equiv S R).injective) ?_ ?_
        (fun W hW => wreath_central_mem_kleinFour j W hW)
      · exact (Wreathed.element_mem_center_iff _ (Nat.one_lt_two_pow (by omega)) _ _ _).mpr
          ⟨rfl, rfl⟩
      · intro h1
        rw [Wreathed.element_base_eq_one_iff] at h1
        exact Wreathed.half_residue_ne_zero j h1.1
  have hxc : QuotientGroup.mk' (CFSG.oddCore K) x ∈ Subgroup.center (K ⧸ CFSG.oddCore K) :=
    (IsQGroup.oddCore_sup_centralizer_center hK S).2 ⟨x, hxS, rfl⟩
  have hdisj : Disjoint (T₁.subgroupOf K) (CFSG.oddCore K) := by
    apply Subgroup.disjoint_of_coprime_natCard
    rw [IsKleinFour.card_four, show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr CFSG.ABGLocalTools.odd_card_oddCore)
  have hfix : ∀ g ∈ Subgroup.normalizer ((T₁.subgroupOf K : Subgroup K) : Set K),
      g * x * g⁻¹ = x := by
    intro g hg
    have h1 : g * x * g⁻¹ * x⁻¹ ∈ T₁.subgroupOf K :=
      Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp hg x).mp hxV) (Subgroup.inv_mem _ hxV)
    have h2 : g * x * g⁻¹ * x⁻¹ ∈ CFSG.oddCore K := by
      have hc := Subgroup.mem_center_iff.mp hxc (QuotientGroup.mk' (CFSG.oddCore K) g)
      apply (QuotientGroup.eq_one_iff (g * x * g⁻¹ * x⁻¹)).mp
      change QuotientGroup.mk' (CFSG.oddCore K) (g * x * g⁻¹ * x⁻¹) = 1
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc, mul_inv_cancel_right, mul_inv_cancel]
    exact mul_inv_eq_one.mp (Subgroup.disjoint_def.mp hdisj h1 h2)
  rw [automizerIndex_eq_card_range]
  intro h3
  obtain ⟨φ, hφ⟩ := exists_prime_orderOf_dvd_card'
    (G := (T₁.subgroupOf K).normalizerMonoidHom.range) 3 h3
  obtain ⟨g, hgφ⟩ := φ.2
  have hφx : (φ : MulAut (T₁.subgroupOf K)) ⟨x, hxV⟩ = ⟨x, hxV⟩ := by
    rw [← hgφ]
    apply Subtype.ext
    rw [normalizerMonoidHom_apply_coe]
    exact hfix g g.2
  have hsq := kleinFour_mulAut_mul_self (φ : MulAut (T₁.subgroupOf K)) (x := ⟨x, hxV⟩)
    (fun h => hx1 (congrArg Subtype.val h)) hφx
  have hφ2 : φ ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, pow_two, hsq]; rfl)
  have hd := orderOf_dvd_of_pow_eq_one hφ2
  rw [hφ] at hd
  norm_num at hd

end CFSG.Semidihedral.AllPrime
