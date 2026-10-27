module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB516Inner
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bLemma56HW
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bTypesHW

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

namespace Hyp52W

variable {H : Type} [Group H] [Finite H] (h : Hyp52W H)

theorem center_eq_bot_of_row516 (hrow : h.Row516) : center (OddBar h.J) = ⊥ := by
  obtain ⟨p, f, -, -, -, hJ, -⟩ := hrow
  have := isSimpleGroup_of_lieModel_psl_two hJ
  exact center_eq_bot_of_isSimpleGroup_of_isQuasisimple h.isQuasisimple_J

theorem mem_normalizer_J_of_comm (hZ : center (OddBar h.J) = ⊥) {z w : H} (hzJ : z ∈ h.J)
    (hz2 : orderOf z = 2) (hwa : w ∈ centralizer ({h.a} : Set H)) (hwz : w * z = z * w) :
    w ∈ normalizer (h.J : Set H) := by
  by_contra hwN
  have hne : conjugate h.J w⁻¹ ≠ h.J := by
    intro he
    apply hwN
    have := congrArg (fun Y => conjugate Y w) he
    simp only [show ∀ Y : Subgroup H, conjugate (conjugate Y w⁻¹) w = Y from fun Y => by
      rw [conjugate_conjugate, inv_mul_cancel, conjugate_one]] at this
    exact mem_normalizer_of_conjugate_eq this.symm
  obtain ⟨h1, h2⟩ := isPComponent_conjugate_centralizer_singleton h.J_le h.isPComponent_J
    (inv_mem hwa)
  have hzL : z ∈ conjugate h.J w⁻¹ := by
    rw [mem_conjugate_iff, inv_inv, mul_assoc, ← hwz, ← mul_assoc, inv_mul_cancel, one_mul]
    exact hzJ
  obtain ⟨y, hy, rfl⟩ := inf_coreActionKernel_le_of_center_eq_bot hZ
    (mem_inf.mpr ⟨hzJ, h.le_coreActionKernel_of_ne h1 h2 hne hzL⟩)
  have hdvd : orderOf y ∣ Nat.card (pPrimeCore 2 ↥h.J) := by
    have := orderOf_dvd_natCard (⟨y, hy⟩ : pPrimeCore 2 ↥h.J)
    rwa [Subgroup.orderOf_mk] at this
  rw [subtype_apply, Subgroup.orderOf_coe] at hz2
  rw [hz2] at hdvd
  exact absurd (Nat.Coprime.coprime_dvd_right hdvd
    (CFSG.pPrimeCore_coprime_card (p := 2))) (by norm_num)

end Hyp52W

namespace Inner516HW

variable {H : Type} [Group H] [Finite H]

theorem exists_involution_comm (hInv : CFL2InvPair) {J : Subgroup H} {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) (hJlie : Blueprint.LieModel (OddBar J) .PSL 2 p (2 * f)) {z : H}
    (hzJ : z ∈ J) (hz2 : orderOf z = 2) :
    ∃ e : H, orderOf e = 2 ∧ e ≠ z ∧ e ∈ J ∧ e * z = z * e := by
  set πJ := QuotientGroup.mk' (pPrimeCore 2 ↥J) with hπJ
  have hzN : z ∈ normalizer (J : Set H) := le_normalizer hzJ
  have hz2' : z * z = 1 := by rw [← pow_two, ← hz2, pow_orderOf_eq_one]
  set zbar : OddBar J := πJ ⟨z, hzJ⟩ with hzbar
  have hzbar2 : orderOf zbar = 2 := by
    apply orderOf_eq_prime
    · rw [← map_pow]
      have : (⟨z, hzJ⟩ : J) ^ 2 = 1 := Subtype.ext (by
        rw [SubgroupClass.coe_pow, OneMemClass.coe_one, ← hz2, pow_orderOf_eq_one])
      rw [this, map_one]
    · intro he
      rw [hzbar, hπJ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at he
      have hdvd : orderOf (⟨z, hzJ⟩ : J) ∣ Nat.card (pPrimeCore 2 ↥J) := by
        have := orderOf_dvd_natCard (⟨⟨z, hzJ⟩, he⟩ : pPrimeCore 2 ↥J)
        rwa [Subgroup.orderOf_mk] at this
      rw [Subgroup.orderOf_mk, hz2] at hdvd
      exact absurd (Nat.Coprime.coprime_dvd_right hdvd
        (CFSG.pPrimeCore_coprime_card (p := 2))) (by norm_num)
  obtain ⟨ubar, hu2, huz, huc⟩ := hInv (OddBar J) p f hp hp2 hf hJlie zbar hzbar2
  obtain ⟨u₀, rfl⟩ := QuotientGroup.mk_surjective ubar
  have hfix : oddBarConj J ⟨z, hzN⟩ (u₀ : OddBar J) = u₀ := by
    rw [oddBarConj_apply_mk]
    have : ((⟨z * u₀ * z⁻¹, (mem_normalizer_iff.mp hzN u₀).mp u₀.2⟩ : J) : OddBar J) =
        zbar * (u₀ : OddBar J) * zbar⁻¹ := by
      rw [hzbar, hπJ, QuotientGroup.mk'_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
        ← QuotientGroup.mk_mul]
      rfl
    rw [this, ← huc, mul_inv_cancel_right]
  obtain ⟨u', hu', hu'z⟩ := exists_fixed_lift hz2' hfix
  obtain ⟨k, ⟨n, hn⟩, hk⟩ := exists_pow_twoPower_map_eq πJ u' (by
    rw [hπJ, QuotientGroup.mk'_apply, hu', ← orderOf_dvd_iff_pow_eq_one, hu2])
  set e₀ : J := u' ^ k with he₀
  have he₀u : πJ e₀ = (u₀ : OddBar J) := by rw [he₀, hk, hπJ, QuotientGroup.mk'_apply, hu']
  have he₀1 : e₀ ≠ 1 := fun he => by
    rw [he, map_one] at he₀u
    rw [← he₀u, orderOf_one] at hu2
    exact absurd hu2 (by norm_num)
  have he₀2 : e₀ ^ 2 = 1 := by
    have hker : e₀ ^ 2 ∈ pPrimeCore 2 ↥J := by
      rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, ← hπJ, map_pow, he₀u,
        ← orderOf_dvd_iff_pow_eq_one, hu2]
    have hdvd1 : orderOf (e₀ ^ 2) ∣ Nat.card (pPrimeCore 2 ↥J) := by
      have := orderOf_dvd_natCard (⟨e₀ ^ 2, hker⟩ : pPrimeCore 2 ↥J)
      rwa [Subgroup.orderOf_mk] at this
    have hdvd2 : orderOf (e₀ ^ 2) ∣ 2 ^ n := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← pow_mul, mul_comm, pow_mul, hn, one_pow]
    have hcop : Nat.Coprime (2 ^ n) (Nat.card (pPrimeCore 2 ↥J)) :=
      Nat.Coprime.pow_left n (CFSG.pPrimeCore_coprime_card (p := 2))
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hdvd2 hdvd1)
  refine ⟨(e₀ : H), ?_, ?_, e₀.2, ?_⟩
  · rw [Subgroup.orderOf_coe]
    exact orderOf_eq_prime he₀2 he₀1
  · intro he
    apply huz
    rw [← he₀u, hzbar]
    congr 1
    exact Subtype.ext he
  · rw [he₀, SubgroupClass.coe_pow]
    exact ((Commute.pow_left (show Commute (u' : H) z from
      (show (z : H) * u' = u' * z from hu'z).symm) k).eq)

theorem exists_core_subgroup {L J : Subgroup H} {a' c e' z : H} {p f : ℕ} {ℓ : OddBar L}
    (hCKmap : ((centralizer ({a'} : Set H)).subgroupOf L).map
      (QuotientGroup.mk' (pPrimeCore 2 ↥L)) = centralizer ({ℓ} : Set (OddBar L)))
    (hzJ : z ∈ J)
    (hτN : ∀ k ∈ (centralizer ({a'} : Set H)).subgroupOf L,
      c⁻¹ * (k : H) * c ∈ normalizer (J : Set H))
    (hτz : ∀ k : ↥L, (c⁻¹ * (k : H) * c) * z = z * (c⁻¹ * (k : H) * c))
    (hsolv : Group.IsSolvable ↥(MulAction.stabilizer (MulAut (OddBar J))
      (QuotientGroup.mk' (pPrimeCore 2 ↥J) ⟨z, hzJ⟩)))
    (h2grp : p ^ f = 3 → IsPGroup 2 ↥(MulAction.stabilizer (MulAut (OddBar J))
      (QuotientGroup.mk' (pPrimeCore 2 ↥J) ⟨z, hzJ⟩)))
    (hconjK : ∀ {k : H}, k ∈ L → e' * k * e'⁻¹ ∈ L) (hea' : e' * a' = a' * e') :
    ∃ Ñ : Subgroup ↥L, Ñ ≤ (centralizer ({a'} : Set H)).subgroupOf L ∧
      Ñ.map (QuotientGroup.mk' (pPrimeCore 2 ↥L)) = centralizerCore516 (p ^ f) ℓ ∧
      (∀ k ∈ Ñ, c⁻¹ * (k : H) * c ∈ coreActionKernel J) ∧
      ∀ k ∈ Ñ, ∃ k' ∈ Ñ, (k' : H) = e' * k * e'⁻¹ := by
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥L) with hπ
  set CK : Subgroup ↥L := (centralizer ({a'} : Set H)).subgroupOf L with hCK
  set N := centralizerCore516 (p ^ f) ℓ with hN
  by_cases hq3 : p ^ f = 3
  ·
    set Ñ : Subgroup ↥L := closure {k : ↥L | k ∈ CK ∧ Odd (orderOf k)} with hÑ
    refine ⟨Ñ, (closure_le _).mpr fun k hk => hk.1, ?_, ?_, ?_⟩
    · rw [hN, centralizerCore516, ite_eq_left hq3, hÑ, MonoidHom.map_closure]
      congr 1
      ext w
      constructor
      · rintro ⟨k, ⟨hk, hkodd⟩, rfl⟩
        refine ⟨hCKmap ▸ mem_map_of_mem π hk, ?_⟩
        exact hkodd.of_dvd_nat (orderOf_map_dvd π k)
      · rintro ⟨hw, hwodd⟩
        rw [← hCKmap] at hw
        obtain ⟨k, hk, rfl⟩ := hw
        obtain ⟨n, hnodd, hne⟩ := exists_pow_odd_orderOf_map_eq π k hwodd
        exact ⟨k ^ n, ⟨pow_mem hk n, hnodd⟩, hne⟩
    · set S' : Subgroup ↥L := ((coreActionKernel J).comap
        (MulAut.conj c⁻¹).toMonoidHom).comap L.subtype with hS'
      have hmemS' : ∀ {k : ↥L}, k ∈ S' ↔ c⁻¹ * (k : H) * c ∈ coreActionKernel J := by
        intro k
        simp only [hS', mem_comap, subtype_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
          inv_inv]
      have hle : Ñ ≤ S' := by
        rw [hÑ, closure_le]
        rintro k ⟨hk, hkodd⟩
        rw [SetLike.mem_coe, hmemS']
        have hodd' : Odd (orderOf (c⁻¹ * (k : H) * c)) := by
          have h1 : c⁻¹ * (k : H) * c = (MulAut.conj c⁻¹).toMonoidHom (k : H) := by
            simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
          rw [h1, orderOf_injective _ (MulAut.conj c⁻¹).injective, Subgroup.orderOf_coe]
          exact hkodd
        exact mem_coreActionKernel_of_odd hzJ (hτN k hk) (hτz k) (h2grp hq3) hodd'
      exact fun k hk => hmemS'.mp (hle hk)
    ·
      set ψ : ↥L →* ↥L :=
        { toFun := fun k => ⟨e' * k * e'⁻¹, hconjK k.2⟩
          map_one' := Subtype.ext (by simp)
          map_mul' := fun k₁ k₂ => Subtype.ext (by simp only [coe_mul]; group) } with hψ
      have hψinj : Function.Injective ψ := fun k₁ k₂ hk => by
        have h1 : e' * (k₁ : H) * e'⁻¹ = e' * k₂ * e'⁻¹ := congrArg Subtype.val hk
        apply Subtype.ext
        calc (k₁ : H) = e'⁻¹ * (e' * k₁ * e'⁻¹) * e' := by group
          _ = e'⁻¹ * (e' * k₂ * e'⁻¹) * e' := by rw [h1]
          _ = k₂ := by group
      have hle : Ñ ≤ Ñ.comap ψ := by
        rw [hÑ, closure_le]
        rintro k ⟨hk, hkodd⟩
        rw [SetLike.mem_coe, mem_comap]
        apply Subgroup.subset_closure
        refine ⟨?_, ?_⟩
        · rw [hCK, mem_subgroupOf, mem_centralizer_singleton_iff]
          show e' * k * e'⁻¹ * a' = a' * (e' * k * e'⁻¹)
          have h1 : (k : H) * a' = a' * k :=
            mem_centralizer_singleton_iff.mp (mem_subgroupOf.mp hk)
          calc e' * k * e'⁻¹ * a' = e' * ((k : H) * (e'⁻¹ * a' * e')) * e'⁻¹ := by group
            _ = e' * ((k : H) * a') * e'⁻¹ := by
              rw [show e'⁻¹ * a' * e' = a' by
                rw [mul_assoc, ← hea', ← mul_assoc, inv_mul_cancel, one_mul]]
            _ = e' * (a' * k) * e'⁻¹ := by rw [h1]
            _ = (e' * a' * e'⁻¹) * (e' * k * e'⁻¹) := by group
            _ = a' * (e' * k * e'⁻¹) := by rw [hea', mul_inv_cancel_right]
        · rw [orderOf_injective ψ hψinj k]
          exact hkodd
      exact fun k hk => ⟨ψ k, hle hk, rfl⟩
  ·
    refine ⟨Quasithin.perfectCore CK, Quasithin.perfectCore_le CK, ?_, ?_, ?_⟩
    · rw [Quasithin.map_perfectCore, hCKmap, hN, centralizerCore516, ite_eq_right hq3]
    · set X : Subgroup H := ((Quasithin.perfectCore CK).map L.subtype).map
        (MulAut.conj c⁻¹).toMonoidHom with hX
      have hmemX : ∀ {k : ↥L}, k ∈ Quasithin.perfectCore CK → c⁻¹ * (k : H) * c ∈ X :=
        fun {k} hk => ⟨k, ⟨k, hk, rfl⟩, by
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]⟩
      have hXC : ∀ x ∈ X, ∃ k ∈ CK, x = c⁻¹ * (k : H) * c := by
        rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
        refine ⟨k, Quasithin.perfectCore_le CK hk, ?_⟩
        simp only [subtype_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      have hXN : X ≤ normalizer (J : Set H) := fun x hx => by
        obtain ⟨k, hk, rfl⟩ := hXC x hx
        exact hτN k hk
      have hXz : ∀ x ∈ X, x * z = z * x := fun x hx => by
        obtain ⟨k, -, rfl⟩ := hXC x hx
        exact hτz k
      have hXperf : ⁅X, X⁆ = X := by
        rw [hX, ← map_commutator, ← map_commutator, Quasithin.perfectCore_perfect]
      have hXle := le_coreActionKernel_of_perfect hzJ hXN hXz hsolv hXperf
      exact fun k hk => hXle (hmemX hk)
    ·
      set ψ : ↥L →* ↥L :=
        { toFun := fun k => ⟨e' * k * e'⁻¹, hconjK k.2⟩
          map_one' := Subtype.ext (by simp)
          map_mul' := fun k₁ k₂ => Subtype.ext (by simp only [coe_mul]; group) } with hψ
      have hCKψ : CK.map ψ ≤ CK := by
        rintro _ ⟨k, hk, rfl⟩
        rw [hCK, mem_subgroupOf, mem_centralizer_singleton_iff]
        show e' * k * e'⁻¹ * a' = a' * (e' * k * e'⁻¹)
        have h1 : (k : H) * a' = a' * k :=
          mem_centralizer_singleton_iff.mp (mem_subgroupOf.mp hk)
        calc e' * k * e'⁻¹ * a' = e' * ((k : H) * (e'⁻¹ * a' * e')) * e'⁻¹ := by group
          _ = e' * ((k : H) * a') * e'⁻¹ := by
            rw [show e'⁻¹ * a' * e' = a' by
              rw [mul_assoc, ← hea', ← mul_assoc, inv_mul_cancel, one_mul]]
          _ = e' * (a' * k) * e'⁻¹ := by rw [h1]
          _ = (e' * a' * e'⁻¹) * (e' * k * e'⁻¹) := by group
          _ = a' * (e' * k * e'⁻¹) := by rw [hea', mul_inv_cancel_right]
      have hle : (Quasithin.perfectCore CK).map ψ ≤ Quasithin.perfectCore CK := by
        rw [Quasithin.map_perfectCore]
        exact Quasithin.perfectCore_mono hCKψ
      exact fun k hk => ⟨ψ k, hle ⟨k, hk, rfl⟩, rfl⟩

theorem oddBarConj_eq_self_of_core {L J : Subgroup H} {CK Ñ : Subgroup ↥L}
    {N : Subgroup (OddBar L)} {c e e' : H} (he' : e' = c * e * c⁻¹)
    (he'N : e' ∈ normalizer (L : Set H)) (heJ : e ∈ J) (hON : pPrimeCore 2 ↥N = ⊥)
    (hNÑ : Ñ.map (QuotientGroup.mk' (pPrimeCore 2 ↥L)) = N) (hÑC : Ñ ≤ CK)
    (hτN : ∀ k ∈ CK, c⁻¹ * (k : H) * c ∈ normalizer (J : Set H))
    (hÑJ : ∀ k ∈ Ñ, c⁻¹ * (k : H) * c ∈ coreActionKernel J)
    (hÑe : ∀ k ∈ Ñ, ∃ k' ∈ Ñ, (k' : H) = e' * k * e'⁻¹) :
    ∀ y ∈ N, oddBarConj L ⟨e', he'N⟩ y = y := by
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥L) with hπ
  set te : ↥(normalizer (L : Set H)) := ⟨e', he'N⟩ with hte
  set ε := oddBarConj L te with hε
  set OJ : Subgroup H := conjugate ((pPrimeCore 2 ↥J).map J.subtype) c⁻¹ with hOJ
  have hOJodd : Nat.Coprime 2 (Nat.card OJ) := by
    rw [hOJ, conjugate, card_map_of_injective (MulAut.conj c⁻¹⁻¹).injective,
      card_map_of_injective J.subtype_injective]
    exact CFSG.pPrimeCore_coprime_card (p := 2)
  set Z₀ : Subgroup ↥L := Ñ ⊓ OJ.comap L.subtype with hZ₀
  have hZ₀map : Z₀.map π = ⊥ := by
    have hZ₀N : Z₀.map π ≤ N := by rw [← hNÑ]; exact map_mono inf_le_left
    have hnorm : ((Z₀.map π).subgroupOf N).Normal := by
      constructor
      intro y hy n
      rw [mem_subgroupOf] at hy ⊢
      obtain ⟨t, ht, hte⟩ := mem_map.mp hy
      have hn : (n : OddBar L) ∈ Ñ.map π := by rw [hNÑ]; exact n.2
      obtain ⟨k₀, hk₀, hk₀e⟩ := mem_map.mp hn
      refine ⟨k₀ * t * k₀⁻¹, mem_inf.mpr ⟨?_, ?_⟩, ?_⟩
      · exact mul_mem (mul_mem hk₀ (mem_inf.mp ht).1) (inv_mem hk₀)
      · have htO : (t : H) ∈ OJ := (mem_inf.mp ht).2
        rw [hOJ, mem_conjugate_iff] at htO
        show ((k₀ * t * k₀⁻¹ : ↥L) : H) ∈ OJ
        rw [hOJ, mem_conjugate_iff]
        have hk₀N : c⁻¹ * (k₀ : H) * c ∈ normalizer (J : Set H) := hτN k₀ (hÑC hk₀)
        have hON := UnbalancedGS.normalizer_le_normalizer_map_of_characteristic J
          (pPrimeCore 2 ↥J) hk₀N
        have := (mem_normalizer_iff.mp hON _).mp htO
        convert this using 1
        simp only [coe_mul, coe_inv, inv_inv]
        group
      · rw [map_mul, map_mul, map_inv, hk₀e, hte]
        rfl
    have hcop : Nat.Coprime 2 (Nat.card ((Z₀.map π).subgroupOf N)) := by
      have h1 : Nat.card ((Z₀.map π).subgroupOf N) = Nat.card (Z₀.map π) := by
        rw [← Subgroup.card_map_of_injective N.subtype_injective, subgroupOf_map_subtype,
          inf_of_le_left hZ₀N]
      have h2 : Nat.card (Z₀.map π) ∣ Nat.card Z₀ := Subgroup.card_map_dvd Z₀ π
      have h3 : Nat.card Z₀ ∣ Nat.card OJ := by
        have hle : Z₀.map L.subtype ≤ OJ := by
          rintro _ ⟨t, ht, rfl⟩
          exact (mem_inf.mp ht).2
        rw [← Subgroup.card_map_of_injective L.subtype_injective]
        exact Subgroup.card_dvd_of_le hle
      rw [h1]
      exact Nat.Coprime.coprime_dvd_right (h2.trans h3) hOJodd
    have hle := LocalAnalysis.ComponentInitial.le_pPrimeCore hnorm hcop
    rw [hON] at hle
    rw [eq_bot_iff]
    intro y hy
    have := hle (mem_subgroupOf.mpr (show ((⟨y, hZ₀N hy⟩ : N) : OddBar L) ∈ Z₀.map π from hy))
    rw [mem_bot] at this ⊢
    exact congrArg Subtype.val this
  intro y hy
  rw [← hNÑ] at hy
  obtain ⟨k, hk, rfl⟩ := hy
  obtain ⟨k', hk'Ñ, hk'e⟩ := hÑe k hk
  have hd : k⁻¹ * k' ∈ Z₀ := by
    refine mem_inf.mpr ⟨mul_mem (inv_mem hk) hk'Ñ, ?_⟩
    rw [mem_comap, subtype_apply, coe_mul, coe_inv, hk'e, hOJ, mem_conjugate_iff]
    have hwK := hÑJ k hk
    obtain ⟨-, hc⟩ := mem_coreActionKernel.mp hwK
    have h1 := hc e heJ
    have heN : e ∈ normalizer (((pPrimeCore 2 ↥J).map J.subtype : Subgroup H) : Set H) :=
      UnbalancedGS.normalizer_le_normalizer_map_of_characteristic J (pPrimeCore 2 ↥J)
        (le_normalizer heJ)
    have h2 := (mem_normalizer_iff.mp heN _).mp h1
    convert h2 using 1
    rw [he', inv_inv]
    group
  have hπd : π (k⁻¹ * k') = 1 := by
    have : π (k⁻¹ * k') ∈ Z₀.map π := mem_map_of_mem π hd
    rw [hZ₀map, mem_bot] at this
    exact this
  have hkk' : π k' = π k := by
    rw [map_mul, map_inv, inv_mul_eq_one] at hπd
    exact hπd.symm
  show oddBarConj L te ((k : ↥L) : OddBar L) = ((k : ↥L) : OddBar L)
  rw [oddBarConj_apply_mk]
  have hkk'' : (⟨(te : H) * k * (te : H)⁻¹, (mem_normalizer_iff.mp te.2 k).mp k.2⟩ : ↥L) =
      k' := Subtype.ext hk'e.symm
  rw [hkk'']
  exact hkk'

end Inner516HW

end CFSG.ComponentClassification.GSThmB
