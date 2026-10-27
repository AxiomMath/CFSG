module

public import CFSG.ClassicalInvolution.Asc77.Lemma310
public import CFSG.ClassicalInvolution.Asc77.ModOApi
public import CFSG.ClassicalInvolution.Asc77.WP1Section6

public section

namespace CFSG.ClassicalInvolution.Asc77.AscP1Nine3

open CFSG.ClassicalInvolution.Asc77 CFSG.Open CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic

variable {G : Type} [Group G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

@[expose] noncomputable def sylowOfIsSylow2In₉ {V P : Subgroup G} (h : IsSylow2In V P) :
    Sylow 2 ↥P where
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

theorem exists_conjSub_eq_sylow [Finite G] (S₁ S₂ : Sylow 2 G) :
    ∃ g : G, conjSub g (S₁ : Subgroup G) = (S₂ : Subgroup G) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S₁ S₂
  refine ⟨g, ?_⟩
  rw [← hg, Sylow.coe_subgroup_smul]
  ext x
  simp [conjSub, Subgroup.pointwise_smul_def]

theorem isSylow2In_inf_of_le_normalizer' [Finite G] {V M H : Subgroup G} (hV : IsSylow2In V M)
    (hHM : H ≤ M) (hn : M ≤ Subgroup.normalizer (H : Set G)) : IsSylow2In (V ⊓ H) H := by
  refine ⟨inf_le_right, hV.2.1.to_le inf_le_left, ?_⟩
  intro T hTH hT2 hle
  obtain ⟨V', hV', hTV'⟩ := IsSylow2In.exists_ge hT2 (hTH.trans hHM)
  obtain ⟨x, hx⟩ := exists_conjSub_eq_sylow (G := ↥M) (sylowOfIsSylow2In₉ hV)
    (sylowOfIsSylow2In₉ hV')
  have hVx : conjSub (x : G) V ≤ M := by
    have := conjSub_mono (n := (x : G)) hV.1
    rwa [conjSub_eq_self_of_mem x.2] at this
  have hV'eq : V' = conjSub (x : G) V := by
    have h1 : (conjSub (x : G) V).subgroupOf M = V'.subgroupOf M := by
      rw [← conjSub_subgroupOf M x V]
      exact hx
    have h2 := Subgroup.subgroupOf_inj.mp h1
    rwa [inf_eq_left.mpr hVx, inf_eq_left.mpr hV'.1, eq_comm] at h2
  have hxH : conjSub (x : G)⁻¹ H = H :=
    mem_normalizer_iff_conjSub_eq.mp ((Subgroup.normalizer (H : Set G)).inv_mem (hn x.2))
  have hTV : conjSub (x : G)⁻¹ T ≤ V ⊓ H := by
    refine le_inf ?_ ?_
    · have := conjSub_mono (n := (x : G)⁻¹) (hTV'.trans hV'eq.le)
      rwa [conjSub_inv_conjSub] at this
    · have := conjSub_mono (n := (x : G)⁻¹) hTH
      rwa [hxH] at this
  have hcard : Nat.card T ≤ Nat.card ↥(V ⊓ H) := by
    have h1 : Nat.card ↥(conjSub (x : G)⁻¹ T) = Nat.card T :=
      (Nat.card_congr (Subgroup.equivMapOfInjective T (MulAut.conj (x : G)⁻¹).toMonoidHom
        (MulAut.conj (x : G)⁻¹).injective).toEquiv).symm
    rw [← h1]
    exact Subgroup.card_le_of_le hTV
  exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm

theorem isSylow2In_inf_of_isSubnormal [Finite G] {S C H : Subgroup G} (hS : IsSylow2In S C)
    (hH : IsSubnormal H C) : IsSylow2In (S ⊓ H) H := by
  induction hH with
  | refl => rwa [inf_eq_left.mpr hS.1]
  | step hHM hn _ ih =>
    have := isSylow2In_inf_of_le_normalizer' (ih hS) hHM
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hHM).mp hn)
    rwa [inf_assoc, inf_eq_right.mpr hHM] at this

theorem exists_orderOf_four_of_four_le [Finite G] {K A : Subgroup G} {z : G}
    (hz : IsUniqueInvolution K z) (hAK : A ≤ K) (hA : IsPGroup 2 A) (h4 : 4 ≤ Nat.card A) :
    ∃ x ∈ A, orderOf x = 4 := by
  by_contra hcon
  have hcon' : ∀ x ∈ A, orderOf x ≠ 4 := fun x hx h => hcon ⟨x, hx, h⟩
  have hsub : ∀ x ∈ A, x = 1 ∨ x = z := by
    intro x hx
    have hxA : IsPGroup 2 ↥(Subgroup.zpowers x) := hA.to_le (Subgroup.zpowers_le.mpr hx)
    obtain ⟨k, hk⟩ := hxA.exists_card_eq
    rw [Nat.card_zpowers] at hk
    have hk1 : k ≤ 1 := by
      by_contra hk2
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
      have hdvd : 2 ^ j ∣ orderOf x := by
        rw [hk]
        exact pow_dvd_pow 2 (by omega)
      have hpow := orderOf_pow_of_dvd (x := x) (by positivity) hdvd
      have h4' : orderOf (x ^ 2 ^ j) = 4 := by
        rw [hpow, hk, Nat.pow_div (by omega) (by norm_num)]
        norm_num
      exact hcon' _ (A.pow_mem hx _) h4'
    have hsq : x * x = 1 := by
      have h2 : orderOf x ∣ 2 := by
        rw [hk]
        calc 2 ^ k ∣ 2 ^ 1 := pow_dvd_pow 2 hk1
          _ = 2 := by norm_num
      rw [← pow_two]
      exact orderOf_dvd_iff_pow_eq_one.mp h2
    exact hz.unique x (hAK hx) hsq
  have := natCard_subgroup_le_two_of_subset (A := A) (a := 1) (b := z) hsub
  omega

theorem conj_eq_or_inv_of_cyclic_four {A : Subgroup G} {x : G}
    (hx : ∀ y ∈ A, y ∈ Subgroup.zpowers x) (hxA : x ∈ A) (hxo : orderOf x = 4) {w : G}
    (hw : conjSub w A = A) : w * x * w⁻¹ = x ∨ w * x * w⁻¹ = x⁻¹ := by
  have hyA : w * x * w⁻¹ ∈ A := by
    have := conj_mem_conjSub (n := w) hxA
    rwa [hw] at this
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hx _ hyA)
  have hyo : orderOf (w * x * w⁻¹) = 4 := by
    have := MulEquiv.orderOf_eq (MulAut.conj w) x
    rw [MulAut.conj_apply, hxo] at this
    exact this
  have hx4 : x ^ 4 = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hxo] at this
  have hmod : x ^ m = x ^ (m % 4) := by
    have := zpow_mod_orderOf x m
    rw [hxo] at this
    simpa using this.symm
  rw [← hm, hmod]
  have h4 : m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3 := by omega
  rcases h4 with h | h | h | h
  · exfalso
    rw [← hm, hmod, h, zpow_zero, orderOf_one] at hyo
    omega
  · left
    rw [h, zpow_one]
  · exfalso
    have : orderOf (x ^ (m % 4)) = 2 := by
      rw [h]
      have h2 := orderOf_pow_of_dvd (x := x) (n := 2) (by norm_num) (by rw [hxo]; norm_num)
      rw [hxo] at h2
      simpa using h2
    rw [← hmod, hm] at this
    omega
  · right
    rw [h]
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast]
    exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact hx4)

theorem uniqueInvolution_restrict {K A : Subgroup G} {z : G} (hz : IsUniqueInvolution K z)
    (hAK : A ≤ K) (hzA : z ∈ A) : IsUniqueInvolution A z where
  mem := hzA
  ne_one := hz.ne_one
  sq := hz.sq
  unique := fun y hy hy2 => hz.unique y (hAK hy) hy2

theorem mem_of_uniqueInvolution_of_isPGroup [Finite G] {K A : Subgroup G} {z : G}
    (hz : IsUniqueInvolution K z) (hAK : A ≤ K) (hA : IsPGroup 2 A) (h2 : 2 ≤ Nat.card A) :
    z ∈ A := by
  have h2dvd : 2 ∣ Nat.card ↥A := by
    rcases hA.card_eq_or_dvd with h | h
    · omega
    · exact h
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 h2dvd
  have htG : orderOf (t : G) = 2 := by rw [Subgroup.orderOf_coe]; exact ht
  have htsq : (t : G) * (t : G) = 1 := by
    have := pow_orderOf_eq_one (t : G)
    rwa [htG, pow_two] at this
  have htne : (t : G) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at htG
    omega
  rcases hz.unique (t : G) (hAK t.2) htsq with h | h
  · exact absurd h htne
  · exact h ▸ t.2

theorem exists_centralizer_orderFour_of_normalizes [Finite G] {K R S : Subgroup G} {z : G}
    (hz : IsUniqueInvolution K z) (hRK : R ≤ K) (hRS : R ≤ S) (hS : IsPGroup 2 S)
    (hzR : z ∈ R) (h4R : 4 ≤ Nat.card R) {d u : G} (hdS : d ∈ S) (huS : u ∈ S)
    (hdR : conjSub d R = R) (huR : conjSub u R = R) :
    ∃ x ∈ R, orderOf x = 4 ∧
      (x * d = d * x ∨ x * u = u * x ∨ x * (d * u) = (d * u) * x) := by
  set P : Subgroup G := R ⊔ Subgroup.closure {d, u} with hP
  have hclS : Subgroup.closure {d, u} ≤ S := by
    rw [Subgroup.closure_le]
    rintro w (rfl | rfl)
    · exact hdS
    · exact huS
  have hPS : P ≤ S := sup_le hRS hclS
  have hP2 : IsPGroup 2 P := hS.to_le hPS
  have hPN : P ≤ Subgroup.normalizer (R : Set G) := by
    refine sup_le Subgroup.le_normalizer ?_
    rw [Subgroup.closure_le]
    rintro w (rfl | rfl)
    · exact mem_normalizer_iff_conjSub_eq.mpr hdR
    · exact mem_normalizer_iff_conjSub_eq.mpr huR
  have hTn : ∀ q ∈ P, conjSub q R = R := fun q hq => mem_normalizer_iff_conjSub_eq.mp (hPN hq)
  have hz' : IsUniqueInvolution R z := uniqueInvolution_restrict hz hRK hzR
  obtain ⟨A, hAR, hAc, hA4, hAP⟩ :=
    exists_invariant_cyclic_order_four hP2 (le_sup_left : R ≤ P) hTn hz' h4R
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥A)
  set x : G := (g : G) with hx
  have hxo : orderOf x = 4 := by
    rw [hx, Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg, hA4]
  have hxA : x ∈ A := g.2
  have hgen : ∀ y ∈ A, y ∈ Subgroup.zpowers x := by
    intro y hy
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨y, hy⟩)
    exact Subgroup.mem_zpowers_iff.mpr ⟨m, by simpa using congrArg Subtype.val hm⟩
  have hdP : d ∈ P := Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
  have huP : u ∈ P := Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
  have hxR : x ∈ R := hAR hxA
  have hdx := conj_eq_or_inv_of_cyclic_four hgen hxA hxo (hAP d hdP)
  have hux := conj_eq_or_inv_of_cyclic_four hgen hxA hxo (hAP u huP)
  have hcomm : ∀ w : G, w * x * w⁻¹ = x → x * w = w * x := by
    intro w h
    calc x * w = (w * x * w⁻¹) * w := by rw [h]
      _ = w * x := by group
  refine ⟨x, hxR, hxo, ?_⟩
  rcases hdx with h | h
  · exact Or.inl (hcomm d h)
  rcases hux with h' | h'
  · exact Or.inr (Or.inl (hcomm u h'))
  · refine Or.inr (Or.inr (hcomm (d * u) ?_))
    calc d * u * x * (d * u)⁻¹ = d * (u * x * u⁻¹) * d⁻¹ := by group
      _ = d * x⁻¹ * d⁻¹ := by rw [h']
      _ = (d * x * d⁻¹)⁻¹ := by group
      _ = x := by rw [h, inv_inv]

theorem commutes_conjSub_of_not_fixed [Finite G] (h67 : L6_7 p f) (hp : p ≠ 2)
    (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω) {K R S : Subgroup G} (hK : K ∈ Ω)
    (hR : IsSylow2In R K) (hRS : R ≤ S) (hS : IsPGroup 2 S) {a : G} (haS : a ∈ S)
    (haK : conjSub a K ≠ K) : Commutes R (conjSub a R) := by
  have hRset : R ∈ RSet Ω := mem_RSet_of_isSylow2In hK hR
  have hRa : conjSub a R ∈ RSet Ω := RSet.conj hΩ.conjInvariant hRset a
  have hRaS : conjSub a R ≤ S := by
    have := conjSub_mono (n := a) hRS
    rwa [conjSub_eq_self_of_mem haS] at this
  obtain ⟨S', hSS'⟩ := hS.exists_le_sylow
  have h4 : 4 ≤ Nat.card R := by
    have := hΩ.eight_le_of_mem_RSet hp hRset
    omega
  have hne : R ≠ conjSub a R := by
    intro h
    apply haK
    refine hΩ.eq_of_le_of_le (hΩ.conjInvariant a K hK) hK hR.2.1 h4 ?_ hR.1
    calc R = conjSub a R := h
      _ ≤ conjSub a K := conjSub_mono hR.1
  exact h67 hp hq G Ω hΩ S' R hRset (conjSub a R) hRa (hRS.trans hSS') (hRaS.trans hSS') hne

theorem eq_one_or_eq_of_mem_inf_conjSub [Finite G] (hΩ : HypOmegaMod p f Ω)
    {K R : Subgroup G} (hK : K ∈ Ω) (hR : IsSylow2In R K) {z : G} (hz : IsUniqueInvolution K z)
    {a : G} (haK : conjSub a K ≠ K) {e : G} (he : e ∈ R ⊓ conjSub a R) : e = 1 ∨ e = z := by
  have hA2 : IsPGroup 2 ↥(R ⊓ conjSub a R) := hR.2.1.to_le inf_le_left
  have hcard : Nat.card ↥(R ⊓ conjSub a R) ≤ 2 :=
    hΩ.card_le_two_of_le_inf hK (hΩ.conjInvariant a K hK) (fun h => haK h.symm) hA2
      (inf_le_left.trans hR.1) (inf_le_right.trans (conjSub_mono hR.1))
  have hdvd : orderOf e ∣ Nat.card ↥(R ⊓ conjSub a R) := Subgroup.orderOf_dvd_natCard _ he
  have hle : orderOf e ≤ 2 :=
    (Nat.le_of_dvd Nat.card_pos hdvd).trans hcard
  have hsq : e * e = 1 := by
    have h2 : orderOf e ∣ 2 := by
      rcases Nat.lt_or_ge (orderOf e) 2 with h | h
      · have : orderOf e = 1 := by
          have := orderOf_pos e
          omega
        rw [this]
        exact one_dvd 2
      · have : orderOf e = 2 := le_antisymm hle h
        rw [this]
    rw [← pow_two]
    exact orderOf_dvd_iff_pow_eq_one.mp h2
  exact hz.unique e (hR.1 he.1) hsq

theorem exists_centralizer_orderFour_of_central [Finite G] {K R : Subgroup G} {z : G}
    (hz : IsUniqueInvolution K z) (hRK : R ≤ K) (hR2 : IsPGroup 2 R) (h8 : 8 ≤ Nat.card R)
    {v : G} (hvR : conjSub v R = R)
    (hcent : ∀ x ∈ R, x⁻¹ * (v * x * v⁻¹) = 1 ∨ x⁻¹ * (v * x * v⁻¹) = z) :
    ∃ x ∈ R, orderOf x = 4 ∧ x * v = v * x := by
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz.sq) hz.ne_one
  have hconj : ∀ x ∈ R, v * x * v⁻¹ ∈ R := fun x hx => hvR ▸ conj_mem_conjSub hx
  have hmem : ∀ x ∈ R, x⁻¹ * (v * x * v⁻¹) ∈ Subgroup.zpowers z := by
    intro x hx
    rcases hcent x hx with h | h
    · rw [h]; exact Subgroup.one_mem _
    · rw [h]; exact Subgroup.mem_zpowers z
  have hmul : ∀ x ∈ R, ∀ y ∈ R, (x * y)⁻¹ * (v * (x * y) * v⁻¹) =
      (x⁻¹ * (v * x * v⁻¹)) * (y⁻¹ * (v * y * v⁻¹)) := by
    intro x hx y hy
    have hc : (x⁻¹ * (v * x * v⁻¹)) * y⁻¹ = y⁻¹ * (x⁻¹ * (v * x * v⁻¹)) := by
      rcases hcent x hx with h | h
      · rw [h]; simp
      · rw [h]
        exact hz.commute_of_mem (K.inv_mem (hRK hy))
    calc (x * y)⁻¹ * (v * (x * y) * v⁻¹)
        = y⁻¹ * ((x⁻¹ * (v * x * v⁻¹)) * (v * y * v⁻¹)) := by group
      _ = (y⁻¹ * (x⁻¹ * (v * x * v⁻¹))) * (v * y * v⁻¹) := by group
      _ = ((x⁻¹ * (v * x * v⁻¹)) * y⁻¹) * (v * y * v⁻¹) := by rw [← hc]
      _ = (x⁻¹ * (v * x * v⁻¹)) * (y⁻¹ * (v * y * v⁻¹)) := by group
  let φ : ↥R →* ↥(Subgroup.zpowers z) :=
    { toFun := fun x => ⟨x⁻¹ * (v * x * v⁻¹), hmem x x.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun x y => by
        apply Subtype.ext
        exact hmul x x.2 y y.2 }
  have hidx : φ.ker.index ≤ 2 := by
    rw [Subgroup.index_ker]
    calc Nat.card φ.range ≤ Nat.card (Subgroup.zpowers z) :=
          Nat.card_le_card_of_injective (Subtype.val : ↥φ.range → ↥(Subgroup.zpowers z))
            Subtype.val_injective
      _ = 2 := by rw [Nat.card_zpowers, hz2]
  have hker4 : 4 ≤ Nat.card φ.ker := by
    have := Subgroup.card_mul_index φ.ker
    have hle : Nat.card φ.ker * φ.ker.index ≤ Nat.card φ.ker * 2 := Nat.mul_le_mul_left _ hidx
    omega
  set A : Subgroup G := φ.ker.map R.subtype with hA
  have hAR : A ≤ R := Subgroup.map_subtype_le _
  have hAcard : Nat.card A = Nat.card φ.ker :=
    (Nat.card_congr (φ.ker.equivMapOfInjective R.subtype R.subtype_injective).toEquiv).symm
  obtain ⟨x, hxA, hxo⟩ := exists_orderOf_four_of_four_le hz (hAR.trans hRK) (hR2.to_le hAR)
    (by omega)
  obtain ⟨y, hy, rfl⟩ := hxA
  refine ⟨(y : G), y.2, hxo, ?_⟩
  have h1 : (y : G)⁻¹ * (v * (y : G) * v⁻¹) = 1 := by
    have := congrArg Subtype.val ((MonoidHom.mem_ker).mp hy)
    exact this
  have h2 : (y : G) = v * (y : G) * v⁻¹ := inv_mul_eq_one.mp h1
  calc (y : G) * v = (v * (y : G) * v⁻¹) * v := by rw [← h2]
    _ = v * y := by group

theorem inv_mul_mem_inf_of_relation {R Ra : Subgroup G} {x x' P Q : G} (hx : x ∈ R)
    (hx' : x' ∈ R) (hP : P ∈ Ra) (hQ : Q ∈ Ra) (h : x' * P = x * Q) : x⁻¹ * x' ∈ R ⊓ Ra := by
  refine ⟨R.mul_mem (R.inv_mem hx) hx', ?_⟩
  have : x⁻¹ * x' = Q * P⁻¹ := by
    calc x⁻¹ * x' = x⁻¹ * (x' * P) * P⁻¹ := by group
      _ = x⁻¹ * (x * Q) * P⁻¹ := by rw [h]
      _ = Q * P⁻¹ := by group
  rw [this]
  exact Ra.mul_mem hQ (Ra.inv_mem hP)

theorem exists_centralizer_orderFour_stab2 [Finite G] (h67 : L6_7 p f) (hp : p ≠ 2)
    (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω) {K R S X : Subgroup G} (hK : K ∈ Ω)
    (hR : IsSylow2In R K) (hRS : R ≤ S) (hS : IsPGroup 2 S) {z : G} (hz : IsUniqueInvolution K z)
    {v a b d : G} (hvS : v ∈ S) (haS : a ∈ S) (hv2 : v * v = 1) (ha2 : a * a = 1)
    (hva : v * a = a * v) (hb : b = v * a) (hvR : conjSub v R = R)
    (haK : conjSub a K ≠ K) (hd : d = v ∨ d = a ∨ d = b) (hXR : R ≤ X) (hXa : conjSub a R ≤ X)
    (hXb : conjSub b R ≤ X)
    (hΓ : ∀ w ∈ ({a, b} : Set G), ∀ y ∈ X, y * w = w * y → y * d = d * y) :
    ∃ x ∈ R, orderOf x = 4 ∧ x * v = v * x := by
  have hRset : R ∈ RSet Ω := mem_RSet_of_isSylow2In hK hR
  have h8 : 8 ≤ Nat.card R := hΩ.eight_le_of_mem_RSet hp hRset
  have hab : a * b = v := by
    rw [hb]
    calc a * (v * a) = (a * v) * a := by group
      _ = (v * a) * a := by rw [← hva]
      _ = v * (a * a) := by group
      _ = v := by rw [ha2, mul_one]
  have hba : b * a = v := by
    rw [hb]
    calc v * a * a = v * (a * a) := by group
      _ = v := by rw [ha2, mul_one]
  have hb2 : b * b = 1 := by
    rw [hb]
    calc v * a * (v * a) = v * (a * v) * a := by group
      _ = v * (v * a) * a := by rw [← hva]
      _ = (v * v) * (a * a) := by group
      _ = 1 := by rw [hv2, ha2, one_mul]
  have hbS : b ∈ S := by rw [hb]; exact S.mul_mem hvS haS
  have hRb : conjSub b R = conjSub a R := by
    rw [hb, hva, conjSub_mul, hvR]
  have hcomm_a : Commutes R (conjSub a R) :=
    commutes_conjSub_of_not_fixed h67 hp hq hΩ hK hR hRS hS haS haK
  have hcomm_b : Commutes R (conjSub b R) := hRb ▸ hcomm_a
  have hcent : ∀ x ∈ R, x⁻¹ * (v * x * v⁻¹) = 1 ∨ x⁻¹ * (v * x * v⁻¹) = z := by
    intro x hx
    have hx'R : v * x * v⁻¹ ∈ R := hvR ▸ conj_mem_conjSub hx
    have hxa : a * x * a⁻¹ ∈ conjSub a R := conj_mem_conjSub hx
    have hxb : b * x * b⁻¹ ∈ conjSub a R := hRb ▸ conj_mem_conjSub hx
    have hx'a : a * (v * x * v⁻¹) * a⁻¹ ∈ conjSub a R := conj_mem_conjSub hx'R
    have hinf : x⁻¹ * (v * x * v⁻¹) ∈ R ⊓ conjSub a R := by
      rcases hd with h | h | h
      ·
        have hyX : x * (a * x * a⁻¹) ∈ X := X.mul_mem (hXR hx) (hXa hxa)
        have hyC := (Subgroup.mem_centralizer_singleton_iff.mp
          (mul_conj_mem_inf_centralizer hRS haS ha2 hcomm_a hx).2)
        have h1 := hΓ a (by simp) _ hyX hyC
        rw [h] at h1
        have h2 : v * (x * (a * x * a⁻¹)) * v⁻¹ = x * (a * x * a⁻¹) := by
          calc v * (x * (a * x * a⁻¹)) * v⁻¹ = (x * (a * x * a⁻¹)) * v * v⁻¹ := by rw [← h1]
            _ = x * (a * x * a⁻¹) := by group
        refine inv_mul_mem_inf_of_relation hx hx'R hx'a hxa ?_
        calc v * x * v⁻¹ * (a * (v * x * v⁻¹) * a⁻¹)
            = v * (x * (a * x * a⁻¹)) * v⁻¹ := by
              calc v * x * v⁻¹ * (a * (v * x * v⁻¹) * a⁻¹)
                  = v * x * v⁻¹ * ((a * v) * x * (a * v)⁻¹) := by group
                _ = v * x * v⁻¹ * ((v * a) * x * (v * a)⁻¹) := by rw [hva]
                _ = v * (x * (a * x * a⁻¹)) * v⁻¹ := by group
          _ = x * (a * x * a⁻¹) := h2
      ·
        have hyX : x * (b * x * b⁻¹) ∈ X := X.mul_mem (hXR hx) (hXb (conj_mem_conjSub hx))
        have hyC := (Subgroup.mem_centralizer_singleton_iff.mp
          (mul_conj_mem_inf_centralizer hRS hbS hb2 hcomm_b hx).2)
        have h1 := hΓ b (by simp) _ hyX hyC
        rw [h] at h1
        have h2 : a * (x * (b * x * b⁻¹)) * a⁻¹ = x * (b * x * b⁻¹) := by
          calc a * (x * (b * x * b⁻¹)) * a⁻¹ = (x * (b * x * b⁻¹)) * a * a⁻¹ := by rw [← h1]
            _ = x * (b * x * b⁻¹) := by group
        have hc : (v * x * v⁻¹) * (a * x * a⁻¹) = (a * x * a⁻¹) * (v * x * v⁻¹) :=
          hcomm_a _ hx'R _ hxa
        refine inv_mul_mem_inf_of_relation hx hx'R hxa hxb ?_
        rw [hc]
        calc a * x * a⁻¹ * (v * x * v⁻¹) = a * (x * (b * x * b⁻¹)) * a⁻¹ := by
              calc a * x * a⁻¹ * (v * x * v⁻¹) = a * x * a⁻¹ * ((a * b) * x * (a * b)⁻¹) := by
                    rw [hab]
                _ = a * (x * (b * x * b⁻¹)) * a⁻¹ := by group
          _ = x * (b * x * b⁻¹) := h2
      ·
        have hyX : x * (a * x * a⁻¹) ∈ X := X.mul_mem (hXR hx) (hXa hxa)
        have hyC := (Subgroup.mem_centralizer_singleton_iff.mp
          (mul_conj_mem_inf_centralizer hRS haS ha2 hcomm_a hx).2)
        have h1 := hΓ a (by simp) _ hyX hyC
        rw [h] at h1
        have h2 : b * (x * (a * x * a⁻¹)) * b⁻¹ = x * (a * x * a⁻¹) := by
          calc b * (x * (a * x * a⁻¹)) * b⁻¹ = (x * (a * x * a⁻¹)) * b * b⁻¹ := by rw [← h1]
            _ = x * (a * x * a⁻¹) := by group
        have hc : (v * x * v⁻¹) * (b * x * b⁻¹) = (b * x * b⁻¹) * (v * x * v⁻¹) :=
          hcomm_b _ hx'R _ (conj_mem_conjSub hx)
        refine inv_mul_mem_inf_of_relation hx hx'R hxb hxa ?_
        rw [hc]
        calc b * x * b⁻¹ * (v * x * v⁻¹) = b * (x * (a * x * a⁻¹)) * b⁻¹ := by
              calc b * x * b⁻¹ * (v * x * v⁻¹) = b * x * b⁻¹ * ((b * a) * x * (b * a)⁻¹) := by
                    rw [hba]
                _ = b * (x * (a * x * a⁻¹)) * b⁻¹ := by group
          _ = x * (a * x * a⁻¹) := h2
    exact eq_one_or_eq_of_mem_inf_conjSub hΩ hK hR hz haK hinf
  exact exists_centralizer_orderFour_of_central hz hR.1 hR.2.1 h8 hvR hcent

theorem false_of_all_move [Finite G] (h67 : L6_7 p f) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : HypOmegaMod p f Ω) {K R S X : Subgroup G} (hK : K ∈ Ω) (hR : IsSylow2In R K)
    (hRS : R ≤ S) (hS : IsPGroup 2 S) {u d : G} (huS : u ∈ S) (hdS : d ∈ S) (hu2 : u * u = 1)
    (huK : conjSub u K ≠ K) (hdK : conjSub d K ≠ K) (hduK : conjSub (d * u) K ≠ K)
    (hXR : R ≤ X) (hXu : conjSub u R ≤ X) (hΓ : ∀ y ∈ X, y * u = u * y → y * d = d * y) :
    False := by
  have hRset : R ∈ RSet Ω := mem_RSet_of_isSylow2In hK hR
  have hquat : IsQuatSub R := hΩ.isQuatSub_of_mem_RSet hp hRset
  have hcomm_u : Commutes R (conjSub u R) :=
    commutes_conjSub_of_not_fixed h67 hp hq hΩ hK hR hRS hS huS huK
  have hcomm_d : Commutes R (conjSub d R) :=
    commutes_conjSub_of_not_fixed h67 hp hq hΩ hK hR hRS hS hdS hdK
  have hcomm_du : Commutes R (conjSub (d * u) R) :=
    commutes_conjSub_of_not_fixed h67 hp hq hΩ hK hR hRS hS (S.mul_mem hdS huS) hduK
  obtain ⟨x, hx, y', hy', hne⟩ := hquat.exists_not_commute
  have hxu : u * x * u⁻¹ ∈ conjSub u R := conj_mem_conjSub hx
  have hyX : x * (u * x * u⁻¹) ∈ X := X.mul_mem (hXR hx) (hXu hxu)
  have hyC := Subgroup.mem_centralizer_singleton_iff.mp
    (mul_conj_mem_inf_centralizer hRS huS hu2 hcomm_u hx).2
  have h1 := hΓ _ hyX hyC
  have h2 : d * (x * (u * x * u⁻¹)) * d⁻¹ = x * (u * x * u⁻¹) := by
    calc d * (x * (u * x * u⁻¹)) * d⁻¹ = (x * (u * x * u⁻¹)) * d * d⁻¹ := by rw [← h1]
      _ = x * (u * x * u⁻¹) := by group
  have hrel : x = (d * x * d⁻¹) * ((d * u) * x * (d * u)⁻¹) * (u * x * u⁻¹)⁻¹ := by
    calc x = (x * (u * x * u⁻¹)) * (u * x * u⁻¹)⁻¹ := by group
      _ = (d * (x * (u * x * u⁻¹)) * d⁻¹) * (u * x * u⁻¹)⁻¹ := by rw [h2]
      _ = _ := by group
  have c1 : Commute y' (u * x * u⁻¹) := (hcomm_u y' hy' _ hxu)
  have c2 : Commute y' (d * x * d⁻¹) := (hcomm_d y' hy' _ (conj_mem_conjSub hx))
  have c3 : Commute y' ((d * u) * x * (d * u)⁻¹) :=
    (hcomm_du y' hy' _ (conj_mem_conjSub hx))
  have hc : Commute y' x := by
    rw [hrel]
    exact (c2.mul_right c3).mul_right c1.inv_right
  exact hne hc.eq.symm

end CFSG.ClassicalInvolution.Asc77.AscP1Nine3
