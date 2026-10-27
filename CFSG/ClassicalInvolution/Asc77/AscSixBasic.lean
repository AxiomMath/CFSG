module

public import CFSG.ClassicalInvolution.QuaternionStructure
public import CFSG.ClassicalInvolution.SmallCases.ConnectedA2DatumTwin
public import CFSG.ClassicalInvolution.Asc77.HypOmegaBasic
public import CFSG.ClassicalInvolution.Asc77.WP1Defs

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open scoped MatrixGroups

theorem ncard_le_two_of_subset_pair {α : Type*} {A : Set α} {a b : α} (h : A ⊆ {a, b}) :
    A.ncard ≤ 2 := by
  calc A.ncard ≤ ({a, b} : Set α).ncard := Set.ncard_le_ncard h (Set.toFinite _)
    _ ≤ ({b} : Set α).ncard + 1 := Set.ncard_insert_le a {b}
    _ = 2 := by rw [Set.ncard_singleton]

theorem natCard_subgroup_le_two_of_subset {α : Type*} [Group α] {A : Subgroup α} {a b : α}
    (h : ∀ x ∈ A, x = a ∨ x = b) : Nat.card A ≤ 2 := by
  have hsub : (A : Set α) ⊆ {a, b} := fun x hx => by
    rcases h x hx with h1 | h1 <;> simp [h1]
  have := ncard_le_two_of_subset_pair hsub
  rwa [← Nat.card_coe_set_eq] at this

theorem le_of_noncentral_mem {α : Type*} [Group α] {J A P : Subgroup α}
    (hex : ∃ v ∈ A, ¬ ∀ w ∈ J, v * w = w * v)
    (hP : ∀ v ∈ A, (¬ ∀ w ∈ J, v * w = w * v) → v ∈ P) : A ≤ P := by
  intro a ha
  by_cases hac : ∀ w ∈ J, a * w = w * a
  · obtain ⟨v₀, hv₀, hv₀c⟩ := hex
    have hav : ¬ ∀ w ∈ J, (a * v₀) * w = w * (a * v₀) := by
      intro h
      apply hv₀c
      intro w hw
      have h1 : Commute a w := hac w hw
      have h2 : Commute (a * v₀) w := h w hw
      have h3 : Commute v₀ w := by
        have := (h1.inv_left).mul_left h2
        simpa [mul_assoc] using this
      exact h3
    have h1 := hP v₀ hv₀ hv₀c
    have h2 := hP (a * v₀) (A.mul_mem ha hv₀) hav
    have := P.mul_mem h2 (P.inv_mem h1)
    simpa using this
  · exact hP a ha hac

theorem eq_or_eq_of_natCard_eq_two_mul {α : Type*} [Group α] [Finite α] {U T R : Subgroup α}
    (hUT : U ≤ T) (hTR : T ≤ R) (hcard : Nat.card R = 2 * Nat.card U) : T = U ∨ T = R := by
  have h1 : Nat.card U ∣ Nat.card T := Subgroup.card_dvd_of_le hUT
  have h2 : Nat.card T ∣ Nat.card R := Subgroup.card_dvd_of_le hTR
  obtain ⟨m, hm⟩ := h1
  have hU0 : 0 < Nat.card U := Nat.card_pos
  have h2' : Nat.card U * m ∣ Nat.card U * 2 := by
    rw [← hm, mul_comm (Nat.card U) 2, ← hcard]
    exact h2
  have hm2 : m ∣ 2 := (Nat.mul_dvd_mul_iff_left hU0).mp h2'
  rcases (Nat.dvd_prime Nat.prime_two).mp hm2 with h | h
  · left
    rw [h, mul_one] at hm
    exact (Subgroup.eq_of_le_of_card_ge hUT hm.le).symm
  · right
    rw [h] at hm
    exact Subgroup.eq_of_le_of_card_ge hTR (by rw [hcard, hm]; omega)

variable {G : Type} [Group G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem HypOmega.nonempty_equiv_sl2 (hΩ : HypOmega p f Ω) {K : Subgroup G} (hK : K ∈ Ω) :
    Nonempty (↥K ≃* SL(2, GaloisField p f)) := by
  obtain ⟨z, hz⟩ := hΩ.classical K hK
  exact hz.nonempty_equiv_sl2 (hΩ.exact K hK)

theorem HypOmega.exists_uniqueInvolution [Finite G] (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : HypOmega p f Ω) {K : Subgroup G} (hK : K ∈ Ω) : ∃ z : G, IsUniqueInvolution K z := by
  obtain ⟨z, hz⟩ := hΩ.classical K hK
  exact ⟨z, ConnectedA2.isUniqueInvolution_of_isClassicalMember hp hq hz⟩

theorem HypOmega.center_eq (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmega p f Ω) {K : Subgroup G}
    (hK : K ∈ Ω) {z : G} (hz : IsUniqueInvolution K z) :
    (∀ w ∈ K, z * w = w * z) ∧
      ∀ w ∈ K, (∀ y ∈ K, w * y = y * w) → w = 1 ∨ w = z := by
  obtain ⟨e⟩ := hΩ.nonempty_equiv_sl2 hK
  have hodd := odd_natCard_galoisField hp hq
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz.sq) hz.ne_one
  have hzK : orderOf (⟨z, hz.mem⟩ : K) = 2 := by rw [Subgroup.orderOf_mk]; exact hz2
  have hez : e ⟨z, hz.mem⟩ = -1 := by
    have := (orderOf_eq_two_iff_of_equiv_sl2 hodd e ⟨z, hz.mem⟩).mp hzK
    rw [this]
    simp
  constructor
  · intro w hw
    have hc : e ⟨z, hz.mem⟩ ∈ Subgroup.center SL(2, GaloisField p f) := by
      rw [hez]
      exact (mem_center_sl2_iff _).mpr (Or.inr rfl)
    have hc' : (⟨z, hz.mem⟩ : K) ∈ Subgroup.center K :=
      (mem_center_iff_of_equiv_sl2 e _).mpr hc
    have := Subgroup.mem_center_iff.mp hc' ⟨w, hw⟩
    exact congrArg Subtype.val this.symm
  · intro w hw hcentral
    have hc : (⟨w, hw⟩ : K) ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hcentral g g.2).symm
    have hc' := (mem_center_iff_of_equiv_sl2 e _).mp hc
    rcases (mem_center_sl2_iff _).mp hc' with h1 | h1
    · left
      have : (⟨w, hw⟩ : K) = 1 := e.injective (by rw [h1, map_one])
      exact congrArg Subtype.val this
    · right
      have : (⟨w, hw⟩ : K) = ⟨z, hz.mem⟩ := e.injective (by rw [h1, hez])
      exact congrArg Subtype.val this

theorem HypOmega.card_le_two_of_le_inf [Finite G] (hΩ : HypOmega p f Ω) {K J : Subgroup G}
    (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J) {A : Subgroup G} (hA : IsPGroup 2 A) (hAK : A ≤ K)
    (hAJ : A ≤ J) : Nat.card A ≤ 2 := by
  obtain ⟨n, hn⟩ := hA.exists_card_eq
  have hdvd : Nat.card A ∣ Nat.card ↥(K ⊓ J) := Subgroup.card_dvd_of_le (le_inf hAK hAJ)
  have hN : Nat.card ↥(K ⊓ J) ≠ 0 := Nat.card_pos.ne'
  rw [hn] at hdvd
  have h1 := (padicValNat_dvd_iff_le hN).mp hdvd
  have h2 := (hΩ.omega4 K hK J hJ hKJ).1
  have hn1 : n ≤ 1 := h1.trans h2
  rw [hn]
  calc 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hn1
    _ = 2 := by norm_num

theorem HypOmega.eq_of_le_of_le [Finite G] (hΩ : HypOmega p f Ω) {K J : Subgroup G} (hK : K ∈ Ω)
    (hJ : J ∈ Ω) {A : Subgroup G} (hA : IsPGroup 2 A) (h4 : 4 ≤ Nat.card A) (hAK : A ≤ K)
    (hAJ : A ≤ J) : K = J := by
  by_contra hne
  have := hΩ.card_le_two_of_le_inf hK hJ hne hA hAK hAJ
  omega

theorem HypOmega.commutes_of_twin [Finite G] (hΩ : HypOmega p f Ω) {K J : Subgroup G}
    (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J) {z : G} (hzK : IsUniqueInvolution K z)
    (hzJ : IsUniqueInvolution J z) : Commutes K J := by
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hzK.sq) hzK.ne_one
  have hdvd : 2 ∣ Nat.card ↥(K ⊓ J) := by
    have := Subgroup.orderOf_dvd_natCard (K ⊓ J) (x := z) ⟨hzK.mem, hzJ.mem⟩
    rwa [hz2] at this
  have hN : Nat.card ↥(K ⊓ J) ≠ 0 := Nat.card_pos.ne'
  have h1 := one_le_padicValNat_of_dvd hN hdvd
  obtain ⟨h2, h3⟩ := hΩ.omega4 K hK J hJ hKJ
  exact h3 (le_antisymm h2 h1)

theorem HypOmega.exists_noncentral [Finite G] (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : HypOmega p f Ω) {J : Subgroup G} (hJ : J ∈ Ω) {A : Subgroup G} (hAJ : A ≤ J)
    (hA3 : 3 ≤ Nat.card A) : ∃ v ∈ A, ¬ ∀ w ∈ J, v * w = w * v := by
  by_contra hcon
  have hcon' : ∀ v ∈ A, ∀ w ∈ J, v * w = w * v := fun v hv w hw => by
    by_contra h
    exact hcon ⟨v, hv, fun hall => h (hall w hw)⟩
  obtain ⟨zJ, hzJ⟩ := hΩ.exists_uniqueInvolution hp hq hJ
  have := natCard_subgroup_le_two_of_subset (A := A) (a := 1) (b := zJ) fun v hv =>
    (hΩ.center_eq hp hq hJ hzJ).2 v (hAJ hv) (hcon' v hv)
  omega

theorem HypOmega.le_normalizer_of_le_centralizer [Finite G] (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : HypOmega p f Ω) {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J) {z : G}
    (hz : IsUniqueInvolution K z) {A : Subgroup G} (hAJ : A ≤ J) (hA2 : IsPGroup 2 A)
    (hA3 : 3 ≤ Nat.card A) (hAc : A ≤ Subgroup.centralizer ({z} : Set G)) :
    A ≤ Subgroup.normalizer (K : Set G) := by
  refine le_of_noncentral_mem (J := J) (hΩ.exists_noncentral hp hq hJ hAJ hA3) ?_
  intro v hv hnc
  have hv2 : IsPGroup 2 (Subgroup.zpowers v) := hA2.to_le (Subgroup.zpowers_le.mpr hv)
  exact hΩ.omega5 K hK J hJ hKJ z hz v (hAJ hv) hnc hv2
    (Subgroup.mem_centralizer_singleton_iff.mp (hAc hv))

theorem IsSylow2In.exists_ge [Finite G] {P T : Subgroup G} (hT : IsPGroup 2 T) (hTP : T ≤ P) :
    ∃ V : Subgroup G, IsSylow2In V P ∧ T ≤ V := by
  obtain ⟨Q, hQ⟩ := IsPGroup.exists_le_sylow (hT.comap_subtype (K := P))
  refine ⟨Q.map P.subtype, ⟨Subgroup.map_subtype_le _, Q.isPGroup'.map _,
    fun V' hV'P hV'2 hle => ?_⟩, ?_⟩
  · have hQV : (Q : Subgroup ↥P) ≤ V'.subgroupOf P := by
      intro x hx
      exact hle ⟨x, hx, rfl⟩
    have hcomap : V'.subgroupOf P = (Q : Subgroup ↥P) :=
      Q.is_maximal' (hV'2.comap_subtype) hQV
    rw [← Subgroup.map_subgroupOf_eq_of_le hV'P, hcomap]
  · intro x hx
    exact ⟨⟨x, hTP hx⟩, hQ hx, rfl⟩

noncomputable def IsSylow2In.toSylow {V P : Subgroup G} (h : IsSylow2In V P) : Sylow 2 ↥P where
  toSubgroup := V.subgroupOf P
  isPGroup' := h.2.1.comap_subtype
  is_maximal' := by
    intro Q hQ hle
    have hVQ : V ≤ Q.map P.subtype := by
      rw [← Subgroup.map_subgroupOf_eq_of_le h.1]
      exact Subgroup.map_mono hle
    have := h.2.2 (Q.map P.subtype) (Subgroup.map_subtype_le _) (hQ.map _) hVQ
    rw [← Subgroup.comap_map_eq_self_of_injective P.subtype_injective Q, this]
    rfl

theorem IsSylow2In.natCard_eq [Finite G] {V V' P : Subgroup G} (h : IsSylow2In V P)
    (h' : IsSylow2In V' P) : Nat.card V = Nat.card V' := by
  have e1 := Sylow.card_eq_multiplicity h.toSylow
  have e2 := Sylow.card_eq_multiplicity h'.toSylow
  have c1 : Nat.card ↥(V.subgroupOf P) = Nat.card V :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.1).toEquiv
  have c2 : Nat.card ↥(V'.subgroupOf P) = Nat.card V' :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h'.1).toEquiv
  have e1' : Nat.card ↥(V.subgroupOf P) = 2 ^ (Nat.card P).factorization 2 := e1
  have e2' : Nat.card ↥(V'.subgroupOf P) = 2 ^ (Nat.card P).factorization 2 := e2
  rw [← c1, ← c2, e1', e2']

theorem IsSylow2In.natCard_le [Finite G] {V P T : Subgroup G} (h : IsSylow2In V P)
    (hT : IsPGroup 2 T) (hTP : T ≤ P) : Nat.card T ≤ Nat.card V := by
  obtain ⟨V', hV', hTV'⟩ := IsSylow2In.exists_ge hT hTP
  rw [h.natCard_eq hV']
  exact Subgroup.card_le_of_le hTV'

theorem IsSylow2In.of_natCard_le [Finite G] {V P T : Subgroup G} (h : IsSylow2In V P)
    (hT : IsPGroup 2 T) (hTP : T ≤ P) (hle : Nat.card V ≤ Nat.card T) : IsSylow2In T P := by
  refine ⟨hTP, hT, fun T' hT'P hT'2 hTT' => ?_⟩
  have h1 := h.natCard_le hT'2 hT'P
  exact (Subgroup.eq_of_le_of_card_ge hTT' (h1.trans hle)).symm

theorem IsSylow2In.eq_of_le {V P T : Subgroup G} (h : IsSylow2In V P) (hT : IsPGroup 2 T)
    (hTP : T ≤ P) (hVT : V ≤ T) : T = V :=
  h.2.2 T hTP hT hVT


section Quat

theorem quat_mem_zpowers_a_one {n : ℕ} [NeZero n] (y : QuaternionGroup n) (hy : 4 < orderOf y) :
    y ∈ Subgroup.zpowers (QuaternionGroup.a 1 : QuaternionGroup n) := by
  cases y with
  | a i =>
    have : (QuaternionGroup.a i : QuaternionGroup n) = (QuaternionGroup.a 1) ^ i.val := by
      rw [QuaternionGroup.a_one_pow, ZMod.natCast_zmod_val]
    rw [this]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
  | xa i =>
    rw [QuaternionGroup.orderOf_xa] at hy
    omega

theorem quat_a_one_xa_zero_not_comm {n : ℕ} [NeZero n] (hn : 2 ≤ n) :
    (QuaternionGroup.a 1 : QuaternionGroup n) * QuaternionGroup.xa 0 ≠
      QuaternionGroup.xa 0 * QuaternionGroup.a 1 := by
  intro h
  rw [QuaternionGroup.a_mul_xa, QuaternionGroup.xa_mul_a] at h
  have h1 : (0 : ZMod (2 * n)) - 1 = 0 + 1 := QuaternionGroup.xa.inj h
  have h2 : ((2 : ℕ) : ZMod (2 * n)) = 0 := by
    push_cast
    linear_combination -h1
  rw [ZMod.natCast_eq_zero_iff] at h2
  have := Nat.le_of_dvd (by norm_num) h2
  omega

end Quat

@[expose] def IsQuatSub (R : Subgroup G) : Prop :=
  ∃ k : ℕ, 1 ≤ k ∧ Nonempty (↥R ≃* QuaternionGroup (2 ^ k))

theorem IsQuatSub.natCard_eq {R : Subgroup G} (h : IsQuatSub R) :
    ∃ k : ℕ, 1 ≤ k ∧ Nat.card R = 2 ^ (k + 2) := by
  obtain ⟨k, hk, ⟨e⟩⟩ := h
  refine ⟨k, hk, ?_⟩
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  ring

theorem IsQuatSub.eight_le {R : Subgroup G} (h : IsQuatSub R) : 8 ≤ Nat.card R := by
  obtain ⟨k, hk, hc⟩ := h.natCard_eq
  rw [hc]
  calc 8 = 2 ^ 3 := by norm_num
    _ ≤ 2 ^ (k + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem IsQuatSub.exists_not_commute {R : Subgroup G} (h : IsQuatSub R) :
    ∃ x ∈ R, ∃ y ∈ R, x * y ≠ y * x := by
  obtain ⟨k, hk, ⟨e⟩⟩ := h
  have h2 : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  refine ⟨((e.symm (QuaternionGroup.a 1) : ↥R) : G), (e.symm (QuaternionGroup.a 1)).2,
    ((e.symm (QuaternionGroup.xa 0) : ↥R) : G), (e.symm (QuaternionGroup.xa 0)).2, fun hc => ?_⟩
  have hc' : e.symm (QuaternionGroup.a 1) * e.symm (QuaternionGroup.xa 0) =
      e.symm (QuaternionGroup.xa 0) * e.symm (QuaternionGroup.a 1) := Subtype.ext hc
  rw [← map_mul, ← map_mul] at hc'
  exact quat_a_one_xa_zero_not_comm h2 (e.symm.injective hc')

theorem IsQuatSub.exists_cyclic_max {R : Subgroup G} (h : IsQuatSub R) :
    ∃ C : Subgroup G, C ≤ R ∧ IsCyclic ↥C ∧ Nat.card R = 2 * Nat.card C ∧
      ∀ y ∈ R, 4 < orderOf y → y ∈ C := by
  obtain ⟨k, hk, ⟨e⟩⟩ := h
  set c₀ : G := ((e.symm (QuaternionGroup.a 1) : ↥R) : G) with hc₀
  have hc₀R : c₀ ∈ R := (e.symm (QuaternionGroup.a 1)).2
  have hord : orderOf c₀ = 2 * 2 ^ k := by
    rw [hc₀, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, QuaternionGroup.orderOf_a_one]
  refine ⟨Subgroup.zpowers c₀, Subgroup.zpowers_le.mpr hc₀R, inferInstance, ?_, ?_⟩
  · rw [Nat.card_zpowers, hord, Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card,
      QuaternionGroup.card]
    ring
  · intro y hy hord4
    have hy' : e ⟨y, hy⟩ ∈ Subgroup.zpowers (QuaternionGroup.a 1 : QuaternionGroup (2 ^ k)) := by
      apply quat_mem_zpowers_a_one
      rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
      exact hord4
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hy'
    refine Subgroup.mem_zpowers_iff.mpr ⟨m, ?_⟩
    have : ((e.symm (QuaternionGroup.a 1)) ^ m : ↥R) = ⟨y, hy⟩ := by
      rw [← map_zpow, hm]
      simp
    simpa [hc₀] using congrArg Subtype.val this

theorem IsQuatSub.exists_cyclic_index_two {R : Subgroup G} (h : IsQuatSub R) :
    ∃ U ≤ R, IsCyclic ↥U ∧ Nat.card R = 2 * Nat.card U := by
  obtain ⟨C, hCR, hC, hcard, -⟩ := h.exists_cyclic_max
  exact ⟨C, hCR, hC, hcard⟩

theorem IsQuatSub.eq_of_cyclic [Finite G] {R U U' : Subgroup G} (h : IsQuatSub R) (hU : U ≤ R)
    (hU' : U' ≤ R) (hcU : IsCyclic ↥U) (hcU' : IsCyclic ↥U') (hcard : Nat.card R = 2 * Nat.card U)
    (hcard' : Nat.card R = 2 * Nat.card U') (h16 : 16 ≤ Nat.card R) : U = U' := by
  obtain ⟨C, hCR, hC, hCcard, hCmem⟩ := h.exists_cyclic_max
  have key : ∀ V : Subgroup G, V ≤ R → IsCyclic ↥V → Nat.card R = 2 * Nat.card V → V = C := by
    intro V hVR hcV hVcard
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥V)
    have hgord : orderOf g = Nat.card V := orderOf_eq_card_of_forall_mem_zpowers hg
    have hg4 : 4 < orderOf (g : G) := by
      rw [Subgroup.orderOf_coe, hgord]
      omega
    have hgC : (g : G) ∈ C := hCmem _ (hVR g.2) hg4
    have hVC : V ≤ C := by
      intro x hx
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨x, hx⟩)
      have : x = (g : G) ^ m := by simpa using (congrArg Subtype.val hm).symm
      rw [this]
      exact Subgroup.zpow_mem _ hgC _
    exact Subgroup.eq_of_le_of_card_ge hVC (by omega)
  rw [key U hU hcU hcard, key U' hU' hcU' hcard']

theorem mem_RSet_of_isSylow2In {R J : Subgroup G} (hJ : J ∈ Ω) (h : IsSylow2In R J) :
    R ∈ RSet Ω :=
  mem_RSet_iff.mpr ⟨J, hJ, h.1, h.2.1, h.2.2⟩

theorem exists_isSylow2In_of_mem_RSet {R : Subgroup G} (hR : R ∈ RSet Ω) :
    ∃ J ∈ Ω, IsSylow2In R J := by
  obtain ⟨J, hJ, h1, h2, h3⟩ := mem_RSet_iff.mp hR
  exact ⟨J, hJ, h1, h2, h3⟩

theorem exists_mem_RSet_ge [Finite G] {J T : Subgroup G} (hJ : J ∈ Ω) (hT : IsPGroup 2 T)
    (hTJ : T ≤ J) : ∃ R ∈ RSet Ω, IsSylow2In R J ∧ T ≤ R := by
  obtain ⟨R, hR, hTR⟩ := IsSylow2In.exists_ge hT hTJ
  exact ⟨R, mem_RSet_of_isSylow2In hJ hR, hR, hTR⟩

theorem HypOmega.isQuatSub_of_mem_RSet [Finite G] (hp : p ≠ 2) (hΩ : HypOmega p f Ω)
    {R : Subgroup G} (hR : R ∈ RSet Ω) : IsQuatSub R := by
  obtain ⟨J, hJ, P, rfl⟩ := hR
  obtain ⟨e⟩ := hΩ.nonempty_equiv_sl2 hJ
  have hF : ringChar (GaloisField p f) ≠ 2 := by
    rw [ringChar.eq (GaloisField p f) p]
    exact hp
  obtain ⟨k, hk, ⟨q⟩⟩ := specialLinearGroup_sylow_quaternion (GaloisField p f) hF
    (Sylow.mapSurjective (f := e.toMonoidHom) e.surjective P)
  refine ⟨k, hk, ⟨?_⟩⟩
  have hcoe := Sylow.coe_mapSurjective (f := e.toMonoidHom) e.surjective P
  exact (Subgroup.equivMapOfInjective (P : Subgroup ↥J) J.subtype J.subtype_injective).symm.trans
    ((Subgroup.equivMapOfInjective (P : Subgroup ↥J) e.toMonoidHom e.injective).trans
      ((MulEquiv.subgroupCongr hcoe.symm).trans q))

theorem HypOmega.eight_le_of_mem_RSet [Finite G] (hp : p ≠ 2) (hΩ : HypOmega p f Ω)
    {R : Subgroup G} (hR : R ∈ RSet Ω) : 8 ≤ Nat.card R :=
  (hΩ.isQuatSub_of_mem_RSet hp hR).eight_le

theorem HypOmega.exists_data_of_mem_USet [Finite G] (hp : p ≠ 2) (hΩ : HypOmega p f Ω)
    {U : Subgroup G} (hU : U ∈ USet Ω) :
    ∃ R ∈ RSet Ω, ∃ J ∈ Ω, IsSylow2In R J ∧ U ≤ R ∧ IsCyclic ↥U ∧
      Nat.card R = 2 * Nat.card U ∧ 4 ≤ Nat.card U := by
  obtain ⟨R, hR, hUR, hcyc, hidx⟩ := hU
  obtain ⟨J, hJ, hRJ⟩ := exists_isSylow2In_of_mem_RSet hR
  have h1 := Subgroup.relIndex_mul_card U R
  rw [inf_eq_left.mpr hUR, hidx] at h1
  have h8 := hΩ.eight_le_of_mem_RSet hp hR
  exact ⟨R, hR, J, hJ, hRJ, hUR, hcyc, h1.symm, by omega⟩

theorem mem_USet_of_natCard [Finite G] {U R J : Subgroup G} (hJ : J ∈ Ω) (hRJ : IsSylow2In R J)
    (hUR : U ≤ R) (hc : IsCyclic ↥U) (hcard : Nat.card R = 2 * Nat.card U) : U ∈ USet Ω := by
  refine ⟨R, mem_RSet_of_isSylow2In hJ hRJ, hUR, hc, ?_⟩
  have h1 := Subgroup.relIndex_mul_card U R
  rw [inf_eq_left.mpr hUR, hcard] at h1
  have hU0 : 0 < Nat.card U := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hU0 h1

theorem isPGroup_of_mem_USet [Finite G] (hp : p ≠ 2) (hΩ : HypOmega p f Ω) {U : Subgroup G}
    (hU : U ∈ USet Ω) : IsPGroup 2 U := by
  obtain ⟨R, -, J, -, hRJ, hUR, -⟩ := hΩ.exists_data_of_mem_USet hp hU
  exact hRJ.2.1.to_le hUR

theorem HypOmega.exists_member_of_mem_USet [Finite G] (hp : p ≠ 2) (hΩ : HypOmega p f Ω)
    {U : Subgroup G} (hU : U ∈ USet Ω) : ∃ K ∈ Ω, U ≤ K := by
  obtain ⟨R, -, J, hJ, hRJ, hUR, -⟩ := hΩ.exists_data_of_mem_USet hp hU
  exact ⟨J, hJ, hUR.trans hRJ.1⟩

theorem HypOmega.eq_of_mem_USet [Finite G] (hp : p ≠ 2) (hΩ : HypOmega p f Ω) {U : Subgroup G}
    (hU : U ∈ USet Ω) {K K' : Subgroup G} (hK : K ∈ Ω) (hK' : K' ∈ Ω) (hUK : U ≤ K)
    (hUK' : U ≤ K') : K = K' := by
  obtain ⟨R, -, J, -, hRJ, hUR, -, -, h4⟩ := hΩ.exists_data_of_mem_USet hp hU
  exact hΩ.eq_of_le_of_le hK hK' (hRJ.2.1.to_le hUR) h4 hUK hUK'

theorem mem_normalizer_iff_conjSub_eq {K : Subgroup G} {n : G} :
    n ∈ Subgroup.normalizer (K : Set G) ↔ conjSub n K = K := by
  constructor
  · intro hn
    ext x
    rw [mem_conjSub_iff]
    have := Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (K : Set G)).inv_mem hn) x
    rw [inv_inv] at this
    exact this.symm
  · intro h
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have := conj_mem_conjSub (n := n) hx
      rwa [h] at this
    · intro hx
      rw [← h, mem_conjSub_iff] at hx
      simpa [mul_assoc] using hx

end CFSG.ClassicalInvolution.Asc77
