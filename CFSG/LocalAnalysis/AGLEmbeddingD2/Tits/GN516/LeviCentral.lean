module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.Quasithin.Background.E1Defs

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516

open CFSG.Open
open scoped commutatorElement

@[expose] def LeviAlt (A : Type*) [Group A] : Prop :=
  Group.IsSolvable A ∨ Open.IsQuasisimple (A ⧸ CFSG.pCore 2 A)

section Central

theorem exists_normal_two_subgroup_of_nilpotent {A : Type} [Group A] [Finite A]
    {N : Subgroup A} [N.Normal] [Group.IsNilpotent ↥N] :
    ∃ N₂ : Subgroup A, N₂.Normal ∧ IsPGroup 2 ↥N₂ ∧
      ∀ y ∈ N, (∃ k : ℕ, orderOf y = 2 ^ k) → y ∈ N₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P₂⟩ : Nonempty (Sylow 2 ↥N) := Sylow.nonempty
  set N₂ : Subgroup A := (P₂ : Subgroup ↥N).map N.subtype with hN₂
  have key : ∀ y ∈ N, (∃ k : ℕ, orderOf y = 2 ^ k) → y ∈ N₂ := by
    rintro y hy ⟨k, hk⟩
    set y' : ↥N := ⟨y, hy⟩ with hy'
    have hy'o : orderOf y' = 2 ^ k := by rw [← hk]; exact Subgroup.orderOf_mk y hy
    have hp : IsPGroup 2 ↥(Subgroup.zpowers y') := by
      exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hy'o])
    obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥N P₂ Q
    have hQP : Q = P₂ := by rw [← hg]; exact Sylow.smul_eq_of_normal
    have : y' ∈ (P₂ : Subgroup ↥N) := hQP ▸ hQ (Subgroup.mem_zpowers y')
    exact ⟨y', this, rfl⟩
  refine ⟨N₂, ⟨fun x hx a => ?_⟩, P₂.2.map N.subtype, key⟩
  have hxN : x ∈ N := by
    obtain ⟨x', -, rfl⟩ := hx
    exact x'.2
  have hxo : ∃ k : ℕ, orderOf x = 2 ^ k := by
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 P₂.2) ⟨x', hx'⟩
    exact ⟨k, by simpa using hk⟩
  refine key _ (Subgroup.Normal.conj_mem inferInstance x hxN a) ?_
  obtain ⟨k, hk⟩ := hxo
  exact ⟨k, by rw [← hk]; exact (MulAut.conj a).orderOf_eq x⟩

theorem exists_two_odd_decomp {A : Type*} [Group A] [Finite A] (x : A) :
    ∃ x₂ ∈ Subgroup.zpowers x, ∃ xo ∈ Subgroup.zpowers x, x = x₂ * xo ∧
      (∃ k : ℕ, orderOf x₂ = 2 ^ k) ∧ Odd (orderOf xo) := by
  have hm : orderOf x ≠ 0 := (orderOf_pos x).ne'
  obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_two_pow_mul_odd hm
  have hcop : IsCoprime ((2 ^ a : ℕ) : ℤ) (b : ℤ) := by
    rw [Nat.isCoprime_iff_coprime]
    exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hb)
  obtain ⟨s, t, hst⟩ := hcop
  have hx1 : x = x ^ (t * (b : ℤ)) * x ^ (s * ((2 ^ a : ℕ) : ℤ)) := by
    rw [← zpow_add]
    have : t * (b : ℤ) + s * ((2 ^ a : ℕ) : ℤ) = 1 := by linarith
    rw [this, zpow_one]
  refine ⟨x ^ (t * (b : ℤ)), Subgroup.zpow_mem_zpowers x _, x ^ (s * ((2 ^ a : ℕ) : ℤ)),
    Subgroup.zpow_mem_zpowers x _, hx1, ?_, ?_⟩
  · have h1 : (x ^ (t * (b : ℤ))) ^ (2 ^ a) = 1 := by
      rw [← zpow_natCast, ← zpow_mul]
      have : t * (b : ℤ) * ((2 ^ a : ℕ) : ℤ) = (orderOf x : ℤ) * t := by
        rw [hab]; push_cast; ring
      rw [this, zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow]
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one h1)
    exact ⟨k, hk⟩
  · have h1 : (x ^ (s * ((2 ^ a : ℕ) : ℤ))) ^ b = 1 := by
      rw [← zpow_natCast, ← zpow_mul]
      have : s * ((2 ^ a : ℕ) : ℤ) * (b : ℤ) = (orderOf x : ℤ) * s := by
        rw [hab]; push_cast; ring
      rw [this, zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow]
    exact Odd.of_dvd_nat hb (orderOf_dvd_of_pow_eq_one h1)

theorem exists_decomp_of_map_mem_pCore {A Ā : Type} [Group A] [Finite A] [Group Ā] (φ : A →* Ā)
    (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center A) {n : A}
    (hn : φ n ∈ CFSG.pCore 2 Ā) :
    ∃ y ∈ CFSG.pCore 2 A, ∃ z ∈ φ.ker, Odd (orderOf z) ∧ n = y * z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite Ā := Finite.of_surjective φ hφ
  set N : Subgroup A := (CFSG.pCore 2 Ā).comap φ with hNdef
  have hNn : N.Normal := CFSG.pCore_normal.comap φ
  have hNnil : Group.IsNilpotent ↥N := by
    have : Group.IsNilpotent ↥(CFSG.pCore 2 Ā) := CFSG.pCore_isPGroup.isNilpotent
    refine Subgroup.isNilpotent_of_ker_le_center
      ((φ.comp N.subtype).codRestrict (CFSG.pCore 2 Ā) (fun m => m.2)) ?_
    intro m hm
    have hm1 : φ (m : A) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hm)
    refine Subgroup.mem_center_iff.2 fun g => Subtype.ext ?_
    exact Subgroup.mem_center_iff.1 (hker (MonoidHom.mem_ker.2 hm1)) g
  obtain ⟨N₂, hN₂n, hN₂p, hN₂⟩ := exists_normal_two_subgroup_of_nilpotent (N := N)
  have hN₂le : N₂ ≤ CFSG.pCore 2 A := le_sSup ⟨hN₂n, hN₂p⟩
  obtain ⟨n₂, hn₂, no, hno, hnn, ⟨k, hk⟩, hodd⟩ := exists_two_odd_decomp n
  have hzN : Subgroup.zpowers n ≤ N := (Subgroup.zpowers_le).2 hn
  have hφno : φ no = 1 := by
    have hmem : φ no ∈ CFSG.pCore 2 Ā := (hzN hno)
    obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.1 CFSG.pCore_isPGroup) ⟨φ no, hmem⟩
    have hj' : orderOf (φ no) = 2 ^ j := by simpa using hj
    have hdvd : orderOf (φ no) ∣ orderOf no := orderOf_map_dvd φ no
    have hodd' : Odd (orderOf (φ no)) := Odd.of_dvd_nat hodd hdvd
    have : j = 0 := by
      by_contra hj0
      rw [hj'] at hodd'
      exact (Nat.not_even_iff_odd.2 hodd') ((Nat.even_pow.2 ⟨even_two, hj0⟩))
    rw [this, pow_zero] at hj'
    exact orderOf_eq_one_iff.1 hj'
  exact ⟨n₂, hN₂le (hN₂ n₂ (hzN hn₂) ⟨k, hk⟩), no, hφno, hodd, hnn⟩

theorem centerQuotientEquiv {E Ē : Type*} [Group E] [Group Ē] (ψ : E →* Ē)
    (hψ : Function.Surjective ψ) (hcentral : ∀ e ∈ ψ.ker, e ∈ Subgroup.center E)
    (hperfE : commutator E = ⊤) : Nonempty (E ⧸ Subgroup.center E ≃* Ē ⧸ Subgroup.center Ē) := by
  set Zb := Subgroup.center Ē with hZb
  let χ : E →* Ē ⧸ Zb := (QuotientGroup.mk' Zb).comp ψ
  have hχ : Function.Surjective χ := (QuotientGroup.mk'_surjective Zb).comp hψ
  have hkerχ : χ.ker = Subgroup.center E := by
    ext x
    rw [MonoidHom.mem_ker]
    show (QuotientGroup.mk' Zb) (ψ x) = 1 ↔ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    constructor
    · intro hx
      have hc : ∀ y, ⁅x, y⁆ ∈ Subgroup.center E := fun y => hcentral _ (by
        rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
        exact (Subgroup.mem_center_iff.1 hx (ψ y)).symm)
      let d : E →* ↥(Subgroup.center E) :=
        { toFun := fun y => ⟨⁅x, y⁆, hc y⟩
          map_one' := Subtype.ext (commutatorElement_one_right x)
          map_mul' := fun y y' => Subtype.ext (by
            have e : ⁅x, y * y'⁆ = ⁅x, y⁆ * (y * ⁅x, y'⁆ * y⁻¹) := by
              simp only [commutatorElement_def]; group
            have hy' := Subgroup.mem_center_iff.1 (hc y') y
            show ⁅x, y * y'⁆ = ⁅x, y⁆ * ⁅x, y'⁆
            rw [e, show y * ⁅x, y'⁆ * y⁻¹ = ⁅x, y'⁆ by rw [hy']; group]) }
      have hd : commutator E ≤ d.ker := Abelianization.commutator_subset_ker d
      rw [hperfE] at hd
      refine Subgroup.mem_center_iff.2 fun y => ?_
      have := congrArg Subtype.val (MonoidHom.mem_ker.1 (hd (Subgroup.mem_top y)))
      have h1 : ⁅x, y⁆ = 1 := this
      rw [commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1.symm
    · intro hx
      refine Subgroup.mem_center_iff.2 fun b => ?_
      obtain ⟨a, rfl⟩ := hψ b
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hx a]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hkerχ.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective χ hχ)⟩

theorem leviAlt_of_central_cover {A Ā : Type} [Group A] [Finite A] [Group Ā] (φ : A →* Ā)
    (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center A)
    (hgen : Subgroup.closure {x : A | ∃ k : ℕ, orderOf x = 2 ^ k} = ⊤) (h : LeviAlt Ā) :
    LeviAlt A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite Ā := Finite.of_surjective φ hφ
  rcases h with hs | hq
  · left
    have hc : IsMulCommutative ↥φ.ker :=
      ⟨⟨fun a b => Subtype.ext (Subgroup.mem_center_iff.1 (hker b.2) a)⟩⟩
    have : Group.IsSolvable ↥φ.ker := inferInstance
    exact Group.isSolvable_of_ker_le_range φ.ker.subtype φ (by rw [Subgroup.range_subtype])
  · right
    set pA := CFSG.pCore 2 A with hpA
    set pB := CFSG.pCore 2 Ā with hpB
    have hmap : pA.map φ ≤ pB :=
      le_sSup ⟨CFSG.pCore_normal.map φ hφ, CFSG.pCore_isPGroup.map φ⟩
    have hle : pA ≤ pB.comap φ := Subgroup.map_le_iff_le_comap.1 hmap
    let ψ : A ⧸ pA →* Ā ⧸ pB := QuotientGroup.map pA pB φ hle
    have hψ : Function.Surjective ψ := by
      intro x
      induction x using QuotientGroup.induction_on with
      | H b =>
        obtain ⟨a, rfl⟩ := hφ b
        exact ⟨a, rfl⟩
    have hkerψ : ∀ e ∈ ψ.ker, ∃ z ∈ φ.ker, Odd (orderOf z) ∧ e = (z : A ⧸ pA) := by
      intro e he
      induction e using QuotientGroup.induction_on with
      | H n =>
        have hn : φ n ∈ pB := by
          have := MonoidHom.mem_ker.1 he
          exact (QuotientGroup.eq_one_iff _).1 this
        obtain ⟨y, hy, z, hz, hodd, rfl⟩ := exists_decomp_of_map_mem_pCore φ hφ hker hn
        refine ⟨z, hz, hodd, ?_⟩
        rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff y).2 hy, one_mul]
    have hcentral : ∀ e ∈ ψ.ker, e ∈ Subgroup.center (A ⧸ pA) := by
      intro e he
      obtain ⟨z, hz, -, rfl⟩ := hkerψ e he
      refine Subgroup.mem_center_iff.2 fun g => ?_
      induction g using QuotientGroup.induction_on with
      | H g =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
          Subgroup.mem_center_iff.1 (hker hz) g]
    obtain ⟨hperfB, hsimB⟩ := hq
    have hgenE : Subgroup.closure {x : A ⧸ pA | ∃ k : ℕ, orderOf x = 2 ^ k} = ⊤ := by
      have h1 : (Subgroup.closure {x : A | ∃ k : ℕ, orderOf x = 2 ^ k}).map
          (QuotientGroup.mk' pA) = ⊤ := by
        rw [hgen, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective pA)]
      rw [MonoidHom.map_closure] at h1
      refine eq_top_iff.2 (h1 ▸ Subgroup.closure_mono ?_)
      rintro _ ⟨x, ⟨k, hk⟩, rfl⟩
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
        (hk ▸ orderOf_map_dvd (QuotientGroup.mk' pA) x)
      exact ⟨j, hj⟩
    have hab : ∀ x : Abelianization (A ⧸ pA), ∃ k : ℕ, x ^ 2 ^ k = 1 := by
      have h1 : (Subgroup.closure {x : A ⧸ pA | ∃ k : ℕ, orderOf x = 2 ^ k}).map
          (Abelianization.of : (A ⧸ pA) →* Abelianization (A ⧸ pA)) = ⊤ := by
        have hofs : Function.Surjective
            (Abelianization.of : (A ⧸ pA) →* Abelianization (A ⧸ pA)) := fun y => by
          obtain ⟨t, ht⟩ := QuotientGroup.mk_surjective y
          exact ⟨t, ht⟩
        rw [hgenE, Subgroup.map_top_of_surjective _ hofs]
      rw [MonoidHom.map_closure] at h1
      intro x
      have hx : x ∈ Subgroup.closure
          ((Abelianization.of : (A ⧸ pA) →* Abelianization (A ⧸ pA)) ''
            {x : A ⧸ pA | ∃ k : ℕ, orderOf x = 2 ^ k}) := h1 ▸ Subgroup.mem_top x
      induction hx using Subgroup.closure_induction with
      | mem y hy =>
        obtain ⟨y', ⟨k, hk⟩, rfl⟩ := hy
        exact ⟨k, by rw [← map_pow, ← hk, pow_orderOf_eq_one, map_one]⟩
      | one => exact ⟨0, one_pow _⟩
      | mul y z _ _ hy hz =>
        obtain ⟨a, ha⟩ := hy
        obtain ⟨b, hb⟩ := hz
        refine ⟨max a b, ?_⟩
        have h1 : y ^ 2 ^ max a b = 1 := by
          obtain ⟨c, hc⟩ : 2 ^ a ∣ 2 ^ max a b := pow_dvd_pow 2 (le_max_left a b)
          rw [hc, pow_mul, ha, one_pow]
        have h2 : z ^ 2 ^ max a b = 1 := by
          obtain ⟨c, hc⟩ : 2 ^ b ∣ 2 ^ max a b := pow_dvd_pow 2 (le_max_right a b)
          rw [hc, pow_mul, hb, one_pow]
        rw [mul_pow, h1, h2, mul_one]
      | inv y _ hy =>
        obtain ⟨a, ha⟩ := hy
        exact ⟨a, by rw [inv_pow, ha, inv_one]⟩
    have hmapc : (commutator (A ⧸ pA)).map ψ = commutator (Ā ⧸ pB) := by
      rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective ψ hψ]
    have hperfE : commutator (A ⧸ pA) = ⊤ := by
      rw [eq_top_iff]
      intro e _
      have h1 : ψ e ∈ commutator (Ā ⧸ pB) := hperfB ▸ Subgroup.mem_top _
      rw [← hmapc] at h1
      obtain ⟨c, hc, hce⟩ := h1
      have hz : c⁻¹ * e ∈ ψ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hce, inv_mul_cancel]
      obtain ⟨z, -, hodd, hzeq⟩ := hkerψ _ hz
      have hodd' : Odd (orderOf (c⁻¹ * e)) := by
        rw [hzeq]
        exact Odd.of_dvd_nat hodd (orderOf_map_dvd (QuotientGroup.mk' pA) z)
      obtain ⟨k, hk⟩ := hab (Abelianization.of (c⁻¹ * e))
      have hdvd : orderOf (Abelianization.of (c⁻¹ * e)) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
      have hodd'' : Odd (orderOf (Abelianization.of (c⁻¹ * e))) :=
        Odd.of_dvd_nat hodd' (orderOf_map_dvd _ _)
      have h1' : orderOf (Abelianization.of (c⁻¹ * e)) = 1 := by
        obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
        rw [hj] at hodd'' ⊢
        have : j = 0 := by
          by_contra hj0
          exact (Nat.not_even_iff_odd.2 hodd'') (Nat.even_pow.2 ⟨even_two, hj0⟩)
        rw [this, pow_zero]
      have h2 : c⁻¹ * e ∈ commutator (A ⧸ pA) := by
        have : (Abelianization.of (c⁻¹ * e)) = 1 := orderOf_eq_one_iff.1 h1'
        rw [← Abelianization.ker_of, MonoidHom.mem_ker]
        exact this
      have : e = c * (c⁻¹ * e) := by group
      rw [this]
      exact Subgroup.mul_mem _ hc h2
    have hsimE : IsSimpleGroup ((A ⧸ pA) ⧸ Subgroup.center (A ⧸ pA)) := by
      obtain ⟨e⟩ := centerQuotientEquiv ψ hψ hcentral hperfE
      have := hsimB
      exact e.isSimpleGroup
    exact ⟨hperfE, hsimE⟩

end Central

end CFSG.AGLEmbeddingD2.Tits.GN516
