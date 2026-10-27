module

public import CFSG.LocalAnalysis.ComponentClassification.M12CoverLift
public import CFSG.LocalAnalysis.ComponentClassification.M12J2CoverDisplacement
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicEndgame

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Endgame

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoSporadic CFSG.ComponentClassification.RankTwoSporadic.J2End

theorem odd_card_center_of_decomp {G : Type} [Group G] [Finite G] {A : Subgroup G}
    (hA : standardComponentIsStandard A) {n : ℕ} {R P : Subgroup (Equiv.Perm (Fin n))}
    (hPR : P ≤ R) {ψ : normalizer (A : Set G) →* ↥R} (hψ : IsActionHom A (P.subgroupOf R) ψ)
    (hsimp : IsSimpleGroup (↥A ⧸ center ↥A)) (hprime : ¬ (Nat.card (↥A ⧸ center ↥A)).Prime)
    (hbound : ∀ (L : Type) [Group L] [Finite L], CFSG.Assembly.IsQuasisimple L →
      IsPGroup 2 (center L) → Nonempty (L ⧸ center L ≃* ↥A ⧸ center ↥A) →
        Nat.card (center L) ≤ 2)
    {Q : Equiv.Perm (Fin n) → Prop}
    (hlift : ∀ (L : Type) [Group L] [Finite L], CFSG.Assembly.IsQuasisimple L →
      ∀ t : L, orderOf t = 2 → center L = zpowers t → ∀ π : L →* ↥P,
        Function.Surjective π → π.ker = zpowers t → ∀ v : L, orderOf (π v) = 2 →
          Q ((π v : ↥P) : Equiv.Perm (Fin n)) → v ^ 2 = t)
    (hQ1 : ¬ Q 1) {t : normalizer (A : Set G)} (ht2 : (t : G) ^ 2 = 1)
    (hQ : Q ((ψ t : ↥R) : Equiv.Perm (Fin n))) {a : G}
    (ha : a ∈ A) (hat : ψ ⟨a, le_normalizer ha⟩ = ψ t) (hc2 : (a⁻¹ * t) ^ 2 = 1) :
    Odd (Nat.card (center ↥A)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hZ
  have hZ2 : 2 ∣ Nat.card (center ↥A) := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hZ)
  set k := (Nat.card (center ↥A)).factorization 2 with hk
  set O := centerPowRange (↥A) (2 ^ k) with hO
  have hOZ : O ≤ center ↥A := centerPowRange_le_center _
  obtain ⟨z₂, hz₂⟩ := exists_prime_orderOf_dvd_card' (G := center ↥A) 2 hZ2
  have hz₂O : (z₂ : ↥A) ∉ O := by
    intro h
    have h' := odd_orderOf_of_mem_centerPowRange h
    rw [Subgroup.orderOf_coe, hz₂] at h'
    exact absurd h' (by decide)
  have hZbar : center (↥A ⧸ center ↥A) = ⊥ := center_eq_bot_of_not_prime hprime
  have hcL : center (↥A ⧸ O) = (center ↥A).map (QuotientGroup.mk' O) :=
    center_quot_eq_map hZbar hOZ
  have eL : (↥A ⧸ O) ⧸ center (↥A ⧸ O) ≃* ↥A ⧸ center ↥A :=
    (QuotientGroup.quotientMulEquivOfEq hcL).trans
      (QuotientGroup.quotientQuotientEquivQuotient O (center ↥A) hOZ)
  have hperf : commutator (↥A ⧸ O) = ⊤ := by
    have hAp : Group.IsPerfect ↥A := (Group.isPerfect_def).2 hA.1.1
    exact (Group.isPerfect_def).1
      (Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' O) (QuotientGroup.mk'_surjective O))
  have hLq : CFSG.Assembly.IsQuasisimple (↥A ⧸ O) :=
    ⟨hperf, @MulEquiv.isSimpleGroup _ _ _ _ hsimp eL⟩
  have hL2 : IsPGroup 2 (center (↥A ⧸ O)) := by
    rintro ⟨q, hq⟩
    rw [hcL] at hq
    obtain ⟨z, hz, rfl⟩ := hq
    refine ⟨k, Subtype.ext ?_⟩
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one, QuotientGroup.mk'_apply]
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact pow_mem_centerPowRange hz
  have hcard : Nat.card (center (↥A ⧸ O)) ≤ 2 := hbound (↥A ⧸ O) hLq hL2 ⟨eL⟩
  set t₀ : ↥A ⧸ O := QuotientGroup.mk' O (z₂ : ↥A) with ht₀
  have ht₀C : t₀ ∈ center (↥A ⧸ O) := by
    rw [hcL]
    exact ⟨z₂, z₂.2, rfl⟩
  have ht₀1 : t₀ ≠ 1 := by
    rw [ht₀, QuotientGroup.mk'_apply, Ne, QuotientGroup.eq_one_iff]
    exact hz₂O
  have hz₂sq : (z₂ : ↥A) ^ 2 = 1 := by
    rw [← SubgroupClass.coe_pow, ← hz₂, pow_orderOf_eq_one, OneMemClass.coe_one]
  have ht₀2 : orderOf t₀ = 2 := by
    refine orderOf_eq_prime ?_ ht₀1
    rw [ht₀, ← map_pow, hz₂sq, map_one]
  have hZL : center (↥A ⧸ O) = zpowers t₀ := by
    refine (eq_of_le_of_card_ge (zpowers_le.mpr ht₀C) ?_).symm
    rw [Nat.card_zpowers, ht₀2]
    exact hcard
  let ψA : ↥A →* ↥(P.subgroupOf R) :=
    (ψ.comp (inclusion le_normalizer)).codRestrict (P.subgroupOf R) fun a => hψ.map_mem a a.2
  have hψA : ∀ a : ↥A, ((ψA a : ↥R)) = ψ ⟨a, le_normalizer a.2⟩ := fun _ => rfl
  have hkerA : ψA.ker = center ↥A := by
    ext a
    rw [MonoidHom.mem_ker, ← Subtype.coe_inj, hψA, OneMemClass.coe_one, hψ.eq_one_iff,
      mem_center_iff, mem_centralizer_iff]
    constructor
    · intro h g
      exact Subtype.ext (h g g.2)
    · intro h g hg
      exact congrArg Subtype.val (h ⟨g, hg⟩)
  have hOker : O ≤ ψA.ker := hkerA ▸ hOZ
  let π : ↥A ⧸ O →* ↥P :=
    (subgroupOfEquivOfLe hPR).toMonoidHom.comp (QuotientGroup.lift O ψA hOker)
  have hπ : ∀ a : ↥A, ((π (QuotientGroup.mk' O a) : ↥P) : Equiv.Perm (Fin n)) =
      ((ψ ⟨a, le_normalizer a.2⟩ : ↥R) : Equiv.Perm (Fin n)) := fun _ => rfl
  have hπs : Function.Surjective π := by
    intro p
    obtain ⟨a, ha, hae⟩ := hψ.exists_eq _ ((subgroupOfEquivOfLe hPR).symm p).2
    refine ⟨QuotientGroup.mk' O ⟨a, ha⟩, Subtype.ext ?_⟩
    rw [hπ]
    exact congrArg Subtype.val hae
  have hπk : π.ker = zpowers t₀ := by
    have h1 : π.ker = (QuotientGroup.lift O ψA hOker).ker := by
      ext q
      simp only [MonoidHom.mem_ker, π, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.map_eq_one_iff]
    rw [h1, QuotientGroup.ker_lift, hkerA, ← hcL, hZL]
  have hψt2 : ψ t ^ 2 = 1 := by
    rw [← map_pow, show t ^ 2 = 1 from Subtype.ext (by simpa using ht2), map_one]
  have hψt1 : ψ t ≠ 1 := by
    intro h1
    rw [h1, OneMemClass.coe_one] at hQ
    exact hQ1 hQ
  have hord : orderOf (ψ t) = 2 := orderOf_eq_prime hψt2 hψt1
  set v : ↥A ⧸ O := QuotientGroup.mk' O ⟨a, ha⟩ with hv
  have hπv : ((π v : ↥P) : Equiv.Perm (Fin n)) = ((ψ t : ↥R) : Equiv.Perm (Fin n)) := by
    rw [hv, hπ]
    exact congrArg Subtype.val hat
  have hordv : orderOf (π v) = 2 := by
    rw [← Subgroup.orderOf_coe, hπv, Subgroup.orderOf_coe, hord]
  have hv2 : v ^ 2 = t₀ := hlift _ hLq t₀ ht₀2 hZL π hπs hπk v hordv (by rw [hπv]; exact hQ)
  have ha4 : (⟨a, ha⟩ : ↥A) ^ 4 ∈ O := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    change v ^ 4 = 1
    rw [show v ^ 4 = (v ^ 2) ^ 2 by rw [← pow_mul], hv2]
    exact orderOf_dvd_iff_pow_eq_one.mp (dvd_of_eq ht₀2)
  have ha2 : Even (orderOf ((⟨a, ha⟩ : ↥A) ^ 2)) := by
    by_contra hodd
    obtain ⟨j, hj⟩ := Nat.not_even_iff_odd.mp hodd
    have he : (⟨a, ha⟩ : ↥A) ^ 2 = ((⟨a, ha⟩ : ↥A) ^ 4) ^ (j + 1) := by
      rw [← pow_mul, show 4 * (j + 1) = 2 * (2 * j + 1) + 2 by ring, pow_add, pow_mul, ← hj,
        pow_orderOf_eq_one, one_mul]
    apply ht₀1
    rw [← hv2, hv, ← map_pow, he, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact pow_mem ha4 _
  set c : G := a⁻¹ * t with hc
  have hcK : c ∈ centralizer (A : Set G) := by
    have h1 : ψ ((⟨a, le_normalizer ha⟩ : normalizer (A : Set G))⁻¹ * t) = 1 := by
      rw [map_mul, map_inv, hat, inv_mul_cancel]
    simpa using (hψ.eq_one_iff _).mp h1
  have hac : Commute a c := (mem_centralizer_iff.mp hcK a ha)
  have hc2' : c ^ 2 = (a ^ 2)⁻¹ := by
    have h1 : (a * c) ^ 2 = 1 := by rw [hc, mul_inv_cancel_left]; exact ht2
    rw [hac.mul_pow] at h1
    exact eq_inv_of_mul_eq_one_right h1
  have hc4 : 4 ∣ orderOf c := by
    apply four_dvd_orderOf_of_even
    rw [hc2', orderOf_inv]
    have := ha2
    rwa [← Subgroup.orderOf_coe, SubgroupClass.coe_pow] at this
  have := orderOf_dvd_of_pow_eq_one hc2
  have h42 : 4 ∣ 2 := hc4.trans this
  exact absurd h42 (by norm_num)

end CFSG.ComponentClassification.RankTwoSporadic.Endgame

namespace CFSG.ComponentClassification.RankTwoSporadic.M12

open Subgroup CFSG.Open CFSG.ComponentClassification.RankTwoSporadic
open CFSG.ComponentClassification.M12Cover CFSG.Sporadic.Schreier

theorem m12EquivD_castAdd
    (q : Blueprint.NativeSporadic.M12) (j : Fin 12) :
    (m12EquivD q : Equiv.Perm (Fin 24)) (Fin.castAdd 12 j) =
      Fin.castAdd 12 ((q : Equiv.Perm (Fin 12)) j) := by
  obtain ⟨p, rfl⟩ := m12Proj_bijective.2 q
  rw [m12EquivD_proj]
  exact blockHom_castAdd _ _ j

theorem fixedCount_eq_zero_of_fpf
    (q : Blueprint.NativeSporadic.M12) (h : ∀ p, (m12EquivD q : Equiv.Perm (Fin 24)) p ≠ p) :
    M12Cover.fixedCount q = 0 := by
  rw [M12Cover.fixedCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro j _ hj
  apply h (Fin.castAdd 12 j)
  rw [m12EquivD_castAdd, hj]

theorem m12_odd_card_center
    {G : Type} [Group G] [Finite G] {A : Subgroup G} (hA : standardComponentIsStandard A)
    (e : ↥A ⧸ center ↥A ≃* Blueprint.NativeSporadic.Carrier .M12)
    {ψ : normalizer (A : Set G) →* ↥autModel}
    (hψ : IsActionHom A (blockGroup.subgroupOf autModel) ψ) {t : normalizer (A : Set G)}
    (ht2 : (t : G) ^ 2 = 1) (hfpf : ∀ p, ((ψ t : ↥autModel) : Equiv.Perm (Fin 24)) p ≠ p)
    {a : G} (ha : a ∈ A) (hat : ψ ⟨a, le_normalizer ha⟩ = ψ t) (hc2 : (a⁻¹ * t) ^ 2 = 1) :
    Odd (Nat.card (center ↥A)) := by
  obtain ⟨-, -, hsM⟩ := CFSG.Sporadic.Mathieu.fam_m12_simplicity
  have hsimp : IsSimpleGroup (↥A ⧸ center ↥A) := @MulEquiv.isSimpleGroup _ _ _ _ hsM e
  have hprime : ¬ (Nat.card (↥A ⧸ center ↥A)).Prime := by
    rw [Nat.card_congr e.toEquiv]
    change ¬ (Nat.card Blueprint.NativeSporadic.M12).Prime
    rw [CFSG.Sporadic.Mathieu.card_M12]
    norm_num
  refine Endgame.odd_card_center_of_decomp hA blockGroup_le_autModel hψ hsimp hprime ?_
    (Q := fun σ => ∀ p, σ p ≠ p) ?_ (fun h => h 0 rfl) ht2 hfpf ha hat hc2
  · intro L _ _ hLq hL2 ⟨eL⟩
    exact StandardRecognition.m12J2CentralTwoGroupOrderBound L hLq hL2 (Or.inl ⟨eL.trans e⟩)
  · intro L _ _ hLq t ht hZ π hπ hker v hv hQ
    set π' : L →* Blueprint.NativeSporadic.M12 := m12EquivD.symm.toMonoidHom.comp π with hπ'
    have hπ's : Function.Surjective π' := m12EquivD.symm.surjective.comp hπ
    have hker' : π'.ker = zpowers t := by
      rw [← hker]
      ext l
      simp only [hπ', MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.map_eq_one_iff]
    have hv' : orderOf (π' v) = 2 := by
      rw [hπ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq, hv]
    have hback : m12EquivD (π' v) = π v := by
      rw [hπ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
    have hfix : M12Cover.fixedCount (π' v) = 0 := by
      refine fixedCount_eq_zero_of_fpf _ fun p => ?_
      rw [hback]
      exact hQ p
    exact ((m12_double_cover_involution_lift_orders hLq ht hZ π' hπ's hker').2.2 v hv' hfix).1

end CFSG.ComponentClassification.RankTwoSporadic.M12
