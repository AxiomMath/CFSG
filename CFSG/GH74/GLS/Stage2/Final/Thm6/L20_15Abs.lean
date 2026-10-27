module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.L20_15Gw
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L20_14Pair

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L20

open Subgroup CFSG CFSG.ABGLocalTools CFSG.LocalCores CFSG.GH74.GLS CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Local

section Abs

variable {G : Type} [Group G]

theorem exists_isSylowOf_ge {p : ℕ} [Fact p.Prime] {K W : Subgroup G} (hWK : W ≤ K) (hW : IsPGroup p W) :
    ∃ P : Subgroup G, IsSylowOf p P K ∧ W ≤ P := by
  have hW' : IsPGroup p (W.subgroupOf K) := hW.comap_subtype
  obtain ⟨Q, hQ⟩ := hW'.exists_le_sylow
  refine ⟨(Q : Subgroup K).map K.subtype, ⟨Q, rfl⟩, ?_⟩
  intro x hx
  have : (⟨x, hWK hx⟩ : K) ∈ W.subgroupOf K := hx
  exact ⟨_, hQ this, rfl⟩

theorem isPGroup_Q4 {z y : G} (hz2 : z * z = 1) (hy2 : y * y = 1) (hzy : z * y = y * z) :
    IsPGroup 2 (Q4 z y hz2 hy2 hzy) := by
  intro x
  refine ⟨1, ?_⟩
  apply Subtype.ext
  show (x : G) ^ (2 ^ 1) = 1
  rw [pow_one, sq]
  rcases x.2 with h | h | h | h
  · rw [h]; simp
  · rw [h]; exact hz2
  · rw [h]; exact hy2
  · rw [h]; exact yzyz_eq hz2 hy2 hzy

structure Abs15 (H : Subgroup G) (z y : G) : Prop where
  hzH : z ∈ H
  hyH : y ∈ H
  hz2 : z * z = 1
  hy2 : y * y = 1
  hzy : z * y = y * z
  hne : z ≠ y
  hz1 : z ≠ 1
  hy1 : y ≠ 1
  hu : ¬ IsConj z (y * z)
  hA : ∀ X : Subgroup G, X ≤ H → (∀ x ∈ X, z * x = x * z) → IsPGroup 2 X → y ∈ X →
    ∀ x ∈ X, x = 1 ∨ x = z ∨ x = y ∨ x = y * z
  hF : ∀ e ∈ Fpi {r : ℕ | r.Prime ∧ r ≠ 2} H, (y * z) * e = e * (y * z)
  hO : ∀ N : Subgroup G, N ≤ H → (∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N) → IsPGroup 2 N → y * z ∈ N → False

variable {H : Subgroup G} {z y : G}

theorem Abs15.exists_sylow (a : Abs15 H z y) :
    ∃ V : Subgroup G, IsSylowOf 2 V H ∧ z ∈ V ∧ y ∈ V ∧
      ∀ x ∈ V, z * x = x * z → x = 1 ∨ x = z ∨ x = y ∨ x = y * z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQH : Q4 z y a.hz2 a.hy2 a.hzy ≤ H := by
    rintro x (rfl | rfl | rfl | rfl)
    · exact H.one_mem
    · exact a.hzH
    · exact a.hyH
    · exact H.mul_mem a.hyH a.hzH
  obtain ⟨V, hV, hQV⟩ := exists_isSylowOf_ge hQH (isPGroup_Q4 a.hz2 a.hy2 a.hzy)
  have hzV : z ∈ V := hQV (Or.inr (Or.inl rfl))
  have hyV : y ∈ V := hQV (Or.inr (Or.inr (Or.inl rfl)))
  refine ⟨V, hV, hzV, hyV, ?_⟩
  intro x hxV hxc
  have hX := a.hA (V ⊓ centralizer ({z} : Set G)) (inf_le_left.trans hV.le)
    (fun w hw => (Subgroup.mem_centralizer_singleton_iff.mp hw.2).symm)
    (hV.isPGroup.to_inf_left) ⟨hyV, Subgroup.mem_centralizer_singleton_iff.mpr a.hzy.symm⟩ x
    ⟨hxV, Subgroup.mem_centralizer_singleton_iff.mpr hxc.symm⟩
  exact hX


theorem normal_le_sylow [Finite G] {V : Subgroup G} (hV : IsSylowOf 2 V H) {N : Subgroup G} (hNH : N ≤ H)
    (hN : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N) (hNp : IsPGroup 2 N) : N ≤ V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := hV
  have hnorm : (N.subgroupOf H).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hN g g.2 n hn⟩
  have hp : IsPGroup 2 (N.subgroupOf H) := hNp.comap_subtype
  have hle := hp.le_sylow_of_normal Q
  intro x hx
  have : (⟨x, hNH hx⟩ : H) ∈ N.subgroupOf H := hx
  rw [← hQ]
  exact ⟨_, hle this, rfl⟩


theorem Abs15.big_case [Finite G] (a : Abs15 H z y) {V : Subgroup G} (hV : IsSylowOf 2 V H) (hzV : z ∈ V)
    (hyV : y ∈ V) (hC : ∀ x ∈ V, z * x = x * z → x = 1 ∨ x = z ∨ x = y ∨ x = y * z)
    (h4 : 4 < Nat.card V) :
    (∀ w ∈ V, (∀ v ∈ V, v * w = w * v) → w * w = 1 → w ≠ 1 → w = y * z) ∧
      (∀ N : Subgroup G, N ≤ H → (∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N) → IsPGroup 2 N → N = ⊥) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVp : IsPGroup 2 V := hV.isPGroup
  have huniq := central_unique hVp hzV hyV a.hz2 a.hy2 a.hzy a.hne a.hz1 hC a.hu h4
  refine ⟨huniq, ?_⟩
  intro N hNH hN hNp
  by_contra hN1
  have hNV : N ≤ V := normal_le_sylow hV hNH hN hNp
  obtain ⟨w, hwN, hwc, hw2, hw1⟩ := exists_central_involution_of_normal hVp hNV
    (fun v hv n hn => hN v (hV.le hv) n hn) hN1
  have hwu := huniq w (hNV hwN) hwc hw2 hw1
  apply a.hO N hNH hN hNp
  rw [← hwu]; exact hwN

theorem Em_le (H : Subgroup G) : Em H ≤ H := Subgroup.map_subtype_le _

theorem Em_conj_mem [Finite G] {h : G} (hh : h ∈ H) {j : G} (hj : j ∈ Em H) : h * j * h⁻¹ ∈ Em H := by
  obtain ⟨j', hj', rfl⟩ := hj
  have hc : (layer ↥H).Characteristic := layer_characteristic
  have hn : (layer ↥H).Normal := inferInstance
  exact ⟨⟨h, hh⟩ * j' * ⟨h, hh⟩⁻¹, hn.conj_mem j' hj' _, rfl⟩

theorem Em_perfect (H : Subgroup G) : ⁅Em H, Em H⁆ = Em H := by
  show ⁅(layer ↥H).map H.subtype, (layer ↥H).map H.subtype⁆ = (layer ↥H).map H.subtype
  rw [← Subgroup.map_commutator, layer_perfect]

theorem Em_comm_pPrimeCore [Finite G] (H : Subgroup G) : ∀ a ∈ pPrimeCoreOf 2 H, ∀ l ∈ Em H, a * l = l * a := by
  rintro _ ⟨a', ha', rfl⟩ _ ⟨l', hl', rfl⟩
  exact congrArg Subtype.val (layer_comm_pPrimeCore a' ha' l' hl')

theorem Op_le_Op_Fm [Finite G] (H : Subgroup G) (p : ℕ) [Fact p.Prime] : Op p H ≤ Op p (Fm H) := by
  have hWB : Op p H ≤ Fm H := Subgroup.map_mono (pCore_le_fitting _ p)
  refine le_Op_of_normalized p hWB (fun b hb w hw => ?_) (isPGroup_Op p H)
  have hbH : b ∈ H := (Subgroup.map_subtype_le _) hb
  exact Op_conj_mem (C := H) p (fun c hc b hb => H.mul_mem (H.mul_mem hc hb) (H.inv_mem hc)) hbH hw

theorem Abs15.em_ne_bot [Finite G] (a : Abs15 H z y)
    (hN2 : ∀ w ∈ Op 2 H, (y * z) * w = w * (y * z)) : Em H ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hJ
  have hlay : layer ↥H = ⊥ := by
    have : (layer ↥H).map H.subtype = ⊥ := hJ
    exact Subgroup.map_injective H.subtype_injective (this.trans (Subgroup.map_bot _).symm)
  have huH : y * z ∈ H := H.mul_mem a.hyH a.hzH
  set u' : ↥H := ⟨y * z, huH⟩ with hu'
  have hu1 : y * z ≠ 1 := by
    intro h
    apply a.hne
    have : y = z⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [this]
    exact (inv_eq_of_mul_eq_one_right a.hz2).symm ▸ rfl
  have hu2 : (y * z) * (y * z) = 1 := yzyz_eq a.hz2 a.hy2 a.hzy
  have hFc : ∀ f ∈ fittingSubgroup ↥H, f * u' = u' * f := by
    have hle : fittingSubgroup ↥H ≤ centralizer ({u'} : Set ↥H) := by
      rw [fitting_eq_sup_pCore]
      refine iSup_le fun p => ?_
      intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hpp : p.1.1.Prime := (Nat.mem_primeFactors.mp p.1.2).1
      have : Fact p.1.1.Prime := ⟨hpp⟩
      have hxOp : (x : G) ∈ Op p.1.1 H := ⟨x, hx, rfl⟩
      by_cases hp2 : p.1.1 = 2
      · rw [hp2] at hxOp
        exact Subtype.ext (hN2 _ hxOp).symm
      · have hxF : (x : G) ∈ Fpi {r : ℕ | r.Prime ∧ r ≠ 2} H :=
          (le_iSup₂ (f := fun p (_ : p ∈ {r : ℕ | r.Prime ∧ r ≠ 2}) => Op p (Fm H)) p.1.1 ⟨hpp, hp2⟩)
            (Op_le_Op_Fm H p.1.1 hxOp)
        exact Subtype.ext (a.hF _ hxF).symm
    intro f hf
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hf))
  have hmem : u' ∈ fittingSubgroup ↥H := by
    have h1 : u' ∈ centralizer (generalizedFitting ↥H : Set ↥H) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      have : generalizedFitting ↥H = fittingSubgroup ↥H := by
        simp only [CFSG.generalizedFitting.eq_sup] ; rw [hlay, sup_bot_eq]
      rw [this] at hg
      exact hFc g hg
    have h2 := centralizer_generalizedFitting_le ↥H h1
    have : generalizedFitting ↥H = fittingSubgroup ↥H := by
      simp only [CFSG.generalizedFitting.eq_sup] ; rw [hlay, sup_bot_eq]
    rwa [this] at h2
  have huF : y * z ∈ Fm H := ⟨u', hmem, rfl⟩
  have hord : orderOf (y * z) = 2 := orderOf_eq_prime (by rw [sq]; exact hu2) hu1
  have huOp : y * z ∈ Op 2 (Fm H) := mem_Op_of_orderOf_prime (Fm_isNilpotent H) huF hord
  have hNH : Op 2 (Fm H) ≤ H := (Subgroup.map_subtype_le _).trans (Subgroup.map_subtype_le _)
  exact a.hO (Op 2 (Fm H)) hNH (fun h hh n hn => Op_conj_mem 2 (fun c hc b hb => Fm_conj_mem H hc hb) hh hn)
    (isPGroup_Op 2 (Fm H)) huOp


theorem Em_normalizer [Finite G] (H : Subgroup G) : H ≤ normalizer (Em H : Set G) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro n
  constructor
  · intro hn; exact Em_conj_mem hh hn
  · intro hn
    have := Em_conj_mem (H.inv_mem hh) hn
    simpa [mul_assoc] using this

theorem sylow_inf_Em [Finite G] {V : Subgroup G} (hV : IsSylowOf 2 V H) : IsSylowOf 2 (V ⊓ Em H) (Em H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact hV.inf_of_le_normalizer (Em_le H) (Em_normalizer H)

theorem even_card_of_perfect [Finite G] {J : Subgroup G} (hJp : ⁅J, J⁆ = J) (hJ1 : J ≠ ⊥) : 2 ∣ Nat.card J := by
  by_contra h2
  have hodd : Odd (Nat.card J) := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h2)
  have hsolv := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have hperf : Group.IsPerfect ↥J := Subgroup.isPerfect_iff.mpr hJp
  have : Nontrivial ↥J := (Subgroup.nontrivial_iff_ne_bot J).mpr hJ1
  exact Group.IsPerfect.not_isSolvable ↥J hsolv

theorem ne_bot_of_isSylowOf_even [Finite G] {P J : Subgroup G} (hP : IsSylowOf 2 P J) (h2 : 2 ∣ Nat.card J) :
    P ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hbot
  have hcard := hP.card_eq
  rw [hbot, Subgroup.card_bot] at hcard
  have hpos : 0 < Nat.card J := Nat.card_pos
  have hf : 1 ≤ (Nat.card J).factorization 2 := by
    rw [← Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two hpos.ne']
    exact h2
  have : 2 ^ 1 ∣ 2 ^ (Nat.card J).factorization 2 := pow_dvd_pow 2 hf
  rw [← hcard] at this
  omega

theorem hasDihedral_of_isSylowOf [Finite G] {G₁ Q₀ : Subgroup G} (hQ : IsSylowOf 2 Q₀ G₁) {m : ℕ} (hm : 1 ≤ m)
    (e : ↥Q₀ ≃* DihedralGroup (2 ^ m)) :
    ∀ S : Sylow 2 ↥G₁, ∃ m : ℕ, 1 ≤ m ∧ Nonempty (↥S ≃* DihedralGroup (2 ^ m)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro S
  obtain ⟨Q, hQ'⟩ := hQ
  refine ⟨m, hm, ⟨(Sylow.equiv S Q).trans
    ((Subgroup.equivMapOfInjective _ G₁.subtype G₁.subtype_injective).trans
      ((MulEquiv.subgroupCongr hQ').trans e))⟩⟩

theorem Abs15.not_mem_of_sc [Finite G] (a : Abs15 H z y) {V : Subgroup G} (hV : IsSylowOf 2 V H) (hzV : z ∈ V)
    (hC : ∀ x ∈ V, z * x = x * z → x = 1 ∨ x = z ∨ x = y ∨ x = y * z) (huJ : y * z ∈ Em H) :
    z ∉ Em H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hzJ
  have hVp : IsPGroup 2 V := hV.isPGroup
  have hPJ := sylow_inf_Em hV
  obtain ⟨MV, hMVc, hMVrel⟩ : ∃ M : Subgroup G, IsCyclic M ∧ M.relIndex V ≤ 2 := by
    obtain ⟨M, -, h1, h2⟩ := exists_cyclic_relIndex_le_two hVp hzV a.hz2 a.hz1 hC
    exact ⟨M, h1, h2⟩
  set P := V ⊓ Em H with hP
  set M := MV ⊓ P with hM
  have hMc : IsCyclic ↥M := isCyclic_inf_left hMVc
  have hMP : M ≤ P := inf_le_right
  have hPV : P ≤ V := inf_le_left
  have hPJ' : P ≤ Em H := inf_le_right
  have hMrel : M.relIndex P ≤ 2 := by
    have h1 : M.relIndex P = MV.relIndex P := Subgroup.inf_relIndex_right MV P
    have h2 : MV.relIndex P ≤ MV.relIndex V := by
      have : MV.IsFiniteRelIndex V := Subgroup.isFiniteRelIndex_iff_finiteIndex.mpr inferInstance
      exact Subgroup.relIndex_le_of_le_right hPV Subgroup.relIndex_ne_zero
    omega
  have hperf : commutator ↥(Em H) = ⊤ := by
    have : Group.IsPerfect ↥(Em H) := Subgroup.isPerfect_iff.mpr (Em_perfect H)
    exact this.commutator_eq_top
  have hMJ : M ≤ Em H := hMP.trans hPJ'
  have hSc := single_class_of_perfect (X := ↥(Em H)) hperf (P := P.subgroupOf (Em H)) (M := M.subgroupOf (Em H))
    (((isSylowOf_iff.mp hPJ).2.1).comap_subtype) (isSylowOf_iff.mp hPJ).2.2
    (Subgroup.subgroupOf_mono (Em H) hMP) (isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hMJ).symm
      (Subgroup.subgroupOfEquivOfLe hMJ).symm.surjective)
    (by rw [Subgroup.relIndex_subgroupOf hPJ']; exact hMrel)
    (a := ⟨z, hzJ⟩) (b := ⟨y * z, huJ⟩) (Subtype.ext a.hz2) (Subtype.ext (yzyz_eq a.hz2 a.hy2 a.hzy))
    (fun h => a.hz1 (congrArg Subtype.val h))
    (fun h => by
      have hu1 : y * z ≠ 1 := by
        intro h1
        apply a.hne
        have : y = z⁻¹ := eq_inv_of_mul_eq_one_left h1
        rw [this]
        exact (inv_eq_of_mul_eq_one_right a.hz2).symm ▸ rfl
      exact hu1 (congrArg Subtype.val h))
  obtain ⟨c, hc⟩ := isConj_iff.mp hSc
  exact a.hu (isConj_iff.mpr ⟨(c : G), congrArg Subtype.val hc⟩)


theorem Abs15.main
    [Finite G] (a : Abs15 H z y) :
    y * z ∈ Em H ∧ ∃ r : ℕ, Odd r ∧ PGLModO (Em H) (zpowers z) r := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨V, hV, hzV, hyV, hC⟩ := a.exists_sylow
  have hVp : IsPGroup 2 V := hV.isPGroup
  have huH : y * z ∈ H := H.mul_mem a.hyH a.hzH
  have hu1 : y * z ≠ 1 := by
    intro h1
    apply a.hne
    have : y = z⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [this]
    exact (inv_eq_of_mul_eq_one_right a.hz2).symm ▸ rfl
  have hu2 : (y * z) * (y * z) = 1 := yzyz_eq a.hz2 a.hy2 a.hzy
  have hJp := Em_perfect H
  have hOpN : ∀ h ∈ H, ∀ n ∈ Op 2 H, h * n * h⁻¹ ∈ Op 2 H := fun h hh n hn =>
    Op_conj_mem 2 (fun c hc b hb => H.mul_mem (H.mul_mem hc hb) (H.inv_mem hc)) hh hn
  have hOpH : Op 2 H ≤ H := Subgroup.map_subtype_le _
  by_cases h4 : 4 < Nat.card V
  ·
    obtain ⟨huniq, hNtriv⟩ := a.big_case hV hzV hyV hC h4
    have hN2 : ∀ w ∈ Op 2 H, (y * z) * w = w * (y * z) := by
      intro w hw
      have hbot : Op 2 H = ⊥ := hNtriv (Op 2 H) hOpH hOpN (isPGroup_Op 2 H)
      rw [hbot, Subgroup.mem_bot] at hw
      rw [hw]; simp
    have hJ1 : Em H ≠ ⊥ := a.em_ne_bot hN2
    have hPJ := sylow_inf_Em hV
    have huJ : y * z ∈ Em H := by
      have hP1 : V ⊓ Em H ≠ ⊥ := ne_bot_of_isSylowOf_even hPJ (even_card_of_perfect hJp hJ1)
      obtain ⟨w, hwP, hwc, hw2, hw1⟩ := exists_central_involution_of_normal hVp (inf_le_left : V ⊓ Em H ≤ V)
        (fun v hv n hn => ⟨V.mul_mem (V.mul_mem hv hn.1) (V.inv_mem hv), Em_conj_mem (hV.le hv) hn.2⟩) hP1
      have := huniq w hwP.1 hwc hw2 hw1
      rw [← this]; exact hwP.2
    have hzJ : z ∉ Em H := a.not_mem_of_sc hV hzV hC huJ
    refine ⟨huJ, ?_⟩
    have hJn' : ∀ j ∈ Em H, z * j * z⁻¹ ∈ Em H := fun j hj => Em_conj_mem a.hzH hj
    have hcases : ∀ b ∈ Em H ⊔ zpowers z, b ∈ Em H ∨ b * z ∈ Em H := fun b hb =>
      mem_sup_zpowers_cases a.hz2 hJn' hb
    have hG₁H : Em H ⊔ zpowers z ≤ H := sup_le (Em_le H) ((Subgroup.zpowers_le).mpr a.hzH)
    have hzG₁ : z ∈ Em H ⊔ zpowers z := Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
    have huG₁ : y * z ∈ Em H ⊔ zpowers z := Subgroup.mem_sup_left huJ
    have hyG₁ : y ∈ Em H ⊔ zpowers z := by
      have e : y = (y * z) * z := by rw [mul_assoc, a.hz2, mul_one]
      rw [e]
      exact Subgroup.mul_mem _ huG₁ hzG₁
    have hQ4G₁ : Q4 z y a.hz2 a.hy2 a.hzy ≤ Em H ⊔ zpowers z := by
      rintro x (rfl | rfl | rfl | rfl)
      · exact Subgroup.one_mem _
      · exact hzG₁
      · exact hyG₁
      · exact huG₁
    obtain ⟨Q₀, hQ₀, hQ4⟩ := exists_isSylowOf_ge hQ4G₁ (isPGroup_Q4 a.hz2 a.hy2 a.hzy)
    have hzQ : z ∈ Q₀ := hQ4 (Or.inr (Or.inl rfl))
    have hyQ : y ∈ Q₀ := hQ4 (Or.inr (Or.inr (Or.inl rfl)))
    have hQ₀G₁ : Q₀ ≤ Em H ⊔ zpowers z := hQ₀.le
    have hQ₀H : Q₀ ≤ H := hQ₀G₁.trans hG₁H
    have hC₀ : ∀ x ∈ Q₀, z * x = x * z → x = 1 ∨ x = z ∨ x = y ∨ x = y * z := by
      intro x hxQ hxc
      exact a.hA (Q₀ ⊓ centralizer ({z} : Set G)) (inf_le_left.trans hQ₀H)
        (fun w hw => (Subgroup.mem_centralizer_singleton_iff.mp hw.2).symm)
        (hQ₀.isPGroup.to_inf_left) ⟨hyQ, Subgroup.mem_centralizer_singleton_iff.mpr a.hzy.symm⟩ x
        ⟨hxQ, Subgroup.mem_centralizer_singleton_iff.mpr hxc.symm⟩
    have hRsyl : IsSylowOf 2 (Q₀ ⊓ Em H) (Em H) :=
      hQ₀.inf_of_le_normalizer le_sup_left (hG₁H.trans (Em_normalizer H))
    have hno : (∀ s ∈ Q₀ ⊓ Em H, s ≠ 1 → s * s = 1 → s = y * z) → False := fun huniqR =>
      no_unique_involution (H := H) (J := Em H) (Em_le H) (fun h hh j hj => Em_conj_mem hh hj) hJp
        (Em_comm_pPrimeCore H) huJ hu2 hu1 a.hO (P := Q₀ ⊓ Em H) inf_le_right
        ⟨Q₀.mul_mem hyQ hzQ, huJ⟩ hQ₀.isPGroup.to_inf_left (isSylowOf_iff.mp hRsyl).2.2 huniqR
    obtain ⟨m, hm, ⟨e⟩⟩ := dihedral_sylow hQ₀.isPGroup hzQ hyQ a.hz2 a.hy2 a.hzy a.hne a.hz1 a.hy1 hC₀ a.hu
      (R := Q₀ ⊓ Em H) inf_le_left
      (fun x hx => by
        rcases hcases x (hQ₀G₁ hx) with h | h
        · exact Or.inl ⟨hx, h⟩
        · exact Or.inr ⟨Q₀.mul_mem hx hzQ, h⟩)
      (fun q hq r hr => ⟨Q₀.mul_mem (Q₀.mul_mem hq hr.1) (Q₀.inv_mem hq), Em_conj_mem (hQ₀H hq) hr.2⟩)
      (fun h => hzJ h.2) hno
    exact pgl2_of_dihedral a.hz2 hzJ hJn' hJp huJ hu2 hu1 (hasDihedral_of_isSylowOf hQ₀ hm e)
  ·
    exfalso
    push Not at h4
    have hQV : Q4 z y a.hz2 a.hy2 a.hzy ≤ V := by
      rintro x (rfl | rfl | rfl | rfl)
      · exact V.one_mem
      · exact hzV
      · exact hyV
      · exact V.mul_mem hyV hzV
    have hcardQ := card_Q4 a.hz2 a.hy2 a.hzy a.hz1 a.hy1 a.hne
    have hVeq : Q4 z y a.hz2 a.hy2 a.hzy = V := Subgroup.eq_of_le_of_card_ge hQV (by omega)
    have hVmem : ∀ x ∈ V, x = 1 ∨ x = z ∨ x = y ∨ x = y * z := fun x hx => by
      rw [← hVeq] at hx; exact hx
    have hucomm : ∀ x ∈ V, x * (y * z) = (y * z) * x := by
      intro x hx
      rcases hVmem x hx with rfl | rfl | rfl | rfl
      · simp
      · rw [zyz_eq a.hz2 a.hzy, yzz_eq a.hz2]
      · rw [yyz_eq a.hy2, yzy_eq a.hy2 a.hzy]
      · rfl
    have hN2 : ∀ w ∈ Op 2 H, (y * z) * w = w * (y * z) := fun w hw =>
      (hucomm w (normal_le_sylow hV hOpH hOpN (isPGroup_Op 2 H) hw)).symm
    have hJ1 : Em H ≠ ⊥ := a.em_ne_bot hN2
    have hPJ := sylow_inf_Em hV
    have heven := even_card_of_perfect hJp hJ1
    have hP1 : V ⊓ Em H ≠ ⊥ := ne_bot_of_isSylowOf_even hPJ heven
    by_cases hVJ : V ≤ Em H
    · have hzJ : z ∈ Em H := hVJ hzV
      have huJ : y * z ∈ Em H := hVJ (V.mul_mem hyV hzV)
      exact a.not_mem_of_sc hV hzV hC huJ hzJ
    ·
      set P := V ⊓ Em H with hP
      have hPV : P < V := lt_of_le_of_ne inf_le_left (fun h => hVJ (h ▸ inf_le_right))
      have hcardP : Nat.card P = 2 := by
        have h1 : Nat.card P ∣ Nat.card V := Subgroup.card_dvd_of_le inf_le_left
        have h2 : Nat.card P < Nat.card V := Subgroup.card_lt_of_lt hPV
        have h3 : Nat.card P ≠ 1 := fun h => hP1 (Subgroup.card_eq_one.mp h)
        have h4' : Nat.card V = 4 := by
          have : Nat.card (Q4 z y a.hz2 a.hy2 a.hzy) = Nat.card V := by rw [hVeq]
          omega
        rw [h4'] at h1 h2
        have hpos : 0 < Nat.card P := Nat.card_pos
        interval_cases hc : Nat.card P
        · exact absurd rfl h3
        · rfl
        · exact absurd h1 (by norm_num)
      have hPcyc : IsCyclic ↥P := isCyclic_of_prime_card (p := 2) hcardP
      obtain ⟨w, hwP, hw2, hw1⟩ := exists_involution_of_ne_bot (hVp.to_le (inf_le_left : P ≤ V)) hP1
      have hwJ : w ∈ Em H := hwP.2
      have hperf : commutator ↥(Em H) = ⊤ := by
        have : Group.IsPerfect ↥(Em H) := Subgroup.isPerfect_iff.mpr hJp
        exact this.commutator_eq_top
      obtain ⟨Q, hQ⟩ := hPJ.exists_sylow_eq_subgroupOf
      have hPJle : P ≤ Em H := inf_le_right
      have hQcyc : IsCyclic ↥(Q : Subgroup ↥(Em H)) := by
        have h1 : IsCyclic ↥(P.subgroupOf (Em H)) :=
          isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hPJle).symm
            (Subgroup.subgroupOfEquivOfLe hPJle).symm.surjective
        exact isCyclic_of_surjective (MulEquiv.subgroupCongr hQ.symm)
          (MulEquiv.subgroupCongr hQ.symm).surjective
      refine not_cyclic_sylow_of_perfect hperf Q hQcyc (t := ⟨w, hwJ⟩) (fun h => hw1 (congrArg Subtype.val h))
        ?_ (Subtype.ext hw2)
      rw [hQ]
      exact hwP

end Abs

end CFSG.GH74.GLS.Stage2.Final.Thm6.L20
