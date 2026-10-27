module

public import CFSG.GH74.GLS.C3.Layer1.BackLeaves
public import CFSG.GH74.GLS.Stage1.Main.Gen4NoL34Proof
public import CFSG.GH74.GLS.TwoThin.Basic

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.KGroups CFSG.GH74.KGroups.L34 CFSG.Certificates
  CFSG.Sporadic.Schreier

theorem eq_one_of_isPGroup_of_mem_odd {K : Type*} [Group K] {V N : Subgroup K} (hV : IsPGroup 2 V)
    (hN : Odd (Nat.card N)) {v : K} (hvV : v ∈ V) (hvN : v ∈ N) : v = 1 := by
  obtain ⟨n, hn⟩ := hV ⟨v, hvV⟩
  have h1 : orderOf v ∣ 2 ^ n := by
    apply orderOf_dvd_of_pow_eq_one
    simpa using congrArg Subtype.val hn
  have h2 : orderOf v ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hvN
  have hcop : Nat.Coprime (2 ^ n) (Nat.card N) :=
    Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr hN)
  have : orderOf v ∣ 1 := by
    have := Nat.dvd_gcd h1 h2
    rwa [hcop.gcd_eq_one] at this
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp this)

theorem exists_lift_elem2 {K : Type*} [Group K] [Finite K] (N : Subgroup K) [N.Normal]
    (hN : Odd (Nat.card N)) {E' : Subgroup (K ⧸ N)} (hE : IsPGroup 2 E')
    (hE2 : ∀ e ∈ E', e ^ 2 = 1) :
    ∃ V : Subgroup K, V.map (QuotientGroup.mk' N) = E' ∧ Nat.card V = Nat.card E' ∧
      ∀ v ∈ V, v ^ 2 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨V, hV2, hVmap⟩ := CFSG.LieType.BorelTits.exists_isPGroup_map_eq N hE
  have hinj : ∀ v ∈ V, QuotientGroup.mk' N v = 1 → v = 1 := fun v hv h =>
    eq_one_of_isPGroup_of_mem_odd hV2 hN hv ((QuotientGroup.eq_one_iff v).mp h)
  refine ⟨V, hVmap, ?_, ?_⟩
  · have hinj' : Function.Injective ((QuotientGroup.mk' N).comp V.subtype) := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro v hv
      rw [MonoidHom.mem_ker] at hv
      rw [Subgroup.mem_bot]
      exact Subtype.ext (hinj v v.2 hv)
    have hrange : ((QuotientGroup.mk' N).comp V.subtype).range = V.map (QuotientGroup.mk' N) := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [Nat.card_congr (MonoidHom.ofInjective hinj').toEquiv, hrange, hVmap]
  · intro v hv
    have h1 : QuotientGroup.mk' N v ∈ E' := hVmap ▸ Subgroup.mem_map_of_mem _ hv
    have h2 : (QuotientGroup.mk' N) (v ^ 2) = 1 := by
      rw [map_pow]
      exact hE2 _ h1
    exact hinj (v ^ 2) (V.pow_mem hv 2) h2

theorem exists_E16_of_equiv
    {Kb : Type*} [Group Kb] (ε : Kb ≃* QP.originalSubgroup) :
    ∃ E' : Subgroup Kb, Nat.card E' = 16 ∧ ∀ e ∈ E', e ^ 2 = 1 := by
  have hcard : Nat.card QE.originalSubgroup = 16 := by rw [card_group QE QE_ok, QE_valid.2]
  have hsq := sqOneCheck_sound QE QE_ok QE_sq
  refine ⟨(QE.originalSubgroup.subgroupOf QP.originalSubgroup).map ε.symm.toMonoidHom, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective ε.symm.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe QE_le).toEquiv, hcard]
  · rintro _ ⟨p, hp, rfl⟩
    have hp2 : (p : Equiv.Perm (Fin 42)) ^ 2 = 1 := hsq p hp
    have : p ^ 2 = 1 := Subtype.ext (by simpa using hp2)
    show (ε.symm p) ^ 2 = 1
    rw [← map_pow, this, map_one]

theorem commute_of_sq_eq_one {G : Type*} [Group G] {e f : G} (h1 : e * e = 1) (h2 : f * f = 1)
    (h3 : (e * f) * (e * f) = 1) : e * f = f * e := by
  have hi : e⁻¹ = e := inv_eq_of_mul_eq_one_right h1
  have hj : f⁻¹ = f := inv_eq_of_mul_eq_one_right h2
  have hk : (e * f)⁻¹ = e * f := inv_eq_of_mul_eq_one_right h3
  calc e * f = (e * f)⁻¹ := hk.symm
    _ = f⁻¹ * e⁻¹ := mul_inv_rev e f
    _ = f * e := by rw [hi, hj]

theorem isElemAbelian_closure_insert {G : Type*} [Group G] {E : Subgroup G} (hE : ∀ e ∈ E, e ^ 2 = 1)
    {x : G} (hx : x ^ 2 = 1) (hc : ∀ e ∈ E, x * e = e * x) :
    CFSG.Open.IsElemAbelian 2 (Subgroup.closure ((E : Set G) ∪ {x})) := by
  have hEc : ∀ e ∈ E, ∀ f ∈ E, e * f = f * e := by
    intro e he f hf
    refine commute_of_sq_eq_one ?_ ?_ ?_
    · simpa [sq] using hE e he
    · simpa [sq] using hE f hf
    · simpa [sq] using hE (e * f) (E.mul_mem he hf)
  have hcomm : ∀ a ∈ (E : Set G) ∪ {x}, ∀ b ∈ (E : Set G) ∪ {x}, a * b = b * a := by
    rintro a (ha | ha) b (hb | hb)
    · exact hEc a ha b hb
    · rw [Set.mem_singleton_iff] at hb
      subst hb
      exact (hc a ha).symm
    · rw [Set.mem_singleton_iff] at ha
      subst ha
      exact hc b hb
    · rw [Set.mem_singleton_iff] at ha hb
      rw [ha, hb]
  have hpw : Set.Pairwise ((E : Set G) ∪ {x}) Commute := fun a ha b hb _ => hcomm a ha b hb
  have hcomm' := Subgroup.isMulCommutative_closure hpw
  refine ⟨hcomm', ?_⟩
  intro y hy
  induction hy using Subgroup.closure_induction with
  | mem a ha =>
    rcases ha with ha | ha
    · exact hE a ha
    · rw [Set.mem_singleton_iff] at ha
      rw [ha]
      exact hx
  | one => simp
  | mul a b ha hb iha ihb =>
    have hab : Commute a b := by
      have := mul_comm' (⟨a, ha⟩ : ↥(Subgroup.closure ((E : Set G) ∪ {x}))) ⟨b, hb⟩
      exact congrArg Subtype.val this
    rw [hab.mul_pow, iha, ihb, one_mul]
  | inv a ha iha => simpa using iha

theorem false_of_l34_trivial_center
    {G : Type} [Group G] [Finite G] (hgen : Gen4 G) {x : G}
    (hx : orderOf x = 2) {K : Subgroup G} (hK : IsPCompIn 2 (centralizer ({x} : Set G)) K)
    (hL34 : IsL34Quotient (kBar K)) (hZ : center (kBar K) = ⊥) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNnormal : (pPrimeCore 2 ↥K).Normal := CFSG.pPrimeCore_normal (p := 2) (G := ↥K)
  have hNodd : Odd (Nat.card (pPrimeCore 2 ↥K)) :=
    Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := ↥K))
  obtain ⟨e⟩ := equiv_of_lieModel hL34
  have hq : Function.Bijective (QuotientGroup.mk' (center (kBar K))) := by
    refine ⟨?_, QuotientGroup.mk'_surjective _⟩
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hZ]
  let ε : kBar K ≃* QP.originalSubgroup :=
    (MulEquiv.ofBijective (QuotientGroup.mk' (center (kBar K))) hq).trans e
  obtain ⟨E', hE'card, hE'sq⟩ := exists_E16_of_equiv ε
  have hE'p : IsPGroup 2 E' := IsPGroup.of_card (n := 4) (by rw [hE'card]; norm_num)
  obtain ⟨V, hVmap, hVcard, hVsq⟩ := exists_lift_elem2 (pPrimeCore 2 ↥K) hNodd hE'p hE'sq
  have hV2 : IsPGroup 2 V := IsPGroup.of_card (n := 4) (by rw [hVcard, hE'card]; norm_num)
  set E : Subgroup G := V.map K.subtype with hEdef
  have hEcard : Nat.card E = 16 := by
    rw [hEdef, Subgroup.card_map_of_injective K.subtype_injective, hVcard, hE'card]
  have hEsq : ∀ e ∈ E, e ^ 2 = 1 := by
    rintro _ ⟨v, hv, rfl⟩
    simpa using congrArg Subtype.val (hVsq v hv)
  have hEK : E ≤ K := Subgroup.map_subtype_le V
  have hKcent : ∀ k ∈ K, x * k = k * x := fun k hk =>
    Subgroup.mem_centralizer_iff.mp (hK.1 hk) x (Set.mem_singleton x)
  have hcent : ∀ e ∈ E, x * e = e * x := fun e he => hKcent e (hEK he)
  have hxE : x ∉ E := by
    rintro ⟨v, hv, hvx⟩
    have hvx' : (v : G) = x := hvx
    have hvc : QuotientGroup.mk' (pPrimeCore 2 ↥K) v ∈ center (kBar K) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective g
      show (k : kBar K) * (v : kBar K) = (v : kBar K) * (k : kBar K)
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      apply Subtype.ext
      show (k : G) * (v : G) = (v : G) * (k : G)
      rw [hvx']
      exact (hKcent k k.2).symm
    rw [hZ, Subgroup.mem_bot] at hvc
    have hvN : v ∈ pPrimeCore 2 ↥K := (QuotientGroup.eq_one_iff v).mp hvc
    have hv1 : v = 1 := eq_one_of_isPGroup_of_mem_odd hV2 hNodd hv hvN
    rw [hv1] at hvx'
    have : (1 : G) = x := hvx'
    rw [← this, orderOf_one] at hx
    omega
  have hx2 : x ^ 2 = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx] at this
  have hA := isElemAbelian_closure_insert hEsq hx2 hcent
  have hle := SectionalTwoRankLE.card_le_of_elementary hgen _ hA
  have hEA : E ≤ Subgroup.closure ((E : Set G) ∪ {x}) := fun e he =>
    Subgroup.subset_closure (Or.inl he)
  have hEeq : E = Subgroup.closure ((E : Set G) ∪ {x}) :=
    Subgroup.eq_of_le_of_card_ge hEA (by rw [hEcard]; exact hle)
  exact hxE (hEeq ▸ Subgroup.subset_closure (Or.inr rfl))

theorem b_gen4_noL34_elem_proof :
    B_gen4_noL34_elem := by
  intro G _ _ hgen x K hx hK hbad
  obtain ⟨hL34, hel, -⟩ := hbad
  by_cases hZ : center (kBar K) = ⊥
  · exact false_of_l34_trivial_center hgen hx hK hL34 hZ
  · have hqs : IsQuasisimple (kBar K) := TwoThin.isQuasisimple_hat hK
    have hK4 : Gen4 (kBar K) := Gen4.quotient (pPrimeCore 2 ↥K) (Gen4.subgroup K hgen)
    have hZ2 : IsPGroup 2 ↥(center (kBar K)) := by
      have := hel
      exact CFSG.IsElementaryAbelian.isPGroup 2 _
    exact Stage1.Main.l34_cover_any (kBar K) hqs hZ2 hL34 hZ hK4

end CFSG.GH74.GLS.C3.Layer1.Bk
