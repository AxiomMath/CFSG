module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7Cover
public import CFSG.ClassicalInvolution.SmallCases.Partition

public section

namespace CFSG.ClassicalInvolution.Hat2A7

open CFSG.Open

section Witness

variable {G : Type*} [Group G] {K : Subgroup G}

abbrev OddQuot (K : Subgroup G) : Type _ := ↥K ⧸ classicalInvolutionOddCore ↥K

theorem exists_cover_of_witness (hw : A7Witness K) :
    ∃ (π : OddQuot K →* A7) (z : OddQuot K), IsDoubleCoverA7 π z ∧
      ∀ w : OddQuot K, w ∈ Subgroup.center (OddQuot K) ↔ (w = 1 ∨ w = z) := by
  obtain ⟨hq, hc, ⟨e⟩⟩ := hw
  set E := OddQuot K
  set Z : Subgroup E := Subgroup.center E with hZ
  obtain ⟨z, hz1, hzu⟩ := (Nat.card_eq_two_iff' (1 : Z)).mp hc
  have hZ12 : ∀ w : Z, w = 1 ∨ w = z := fun w => by
    by_cases hw1 : w = 1
    · exact Or.inl hw1
    · exact Or.inr (hzu w hw1)
  let π : E →* A7 := e.toMonoidHom.comp (QuotientGroup.mk' Z)
  have hker : ∀ w : E, π w = 1 ↔ w ∈ Z := fun w => by
    show e (QuotientGroup.mk w) = 1 ↔ w ∈ Z
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  have hcen : ∀ w : E, w ∈ Z ↔ (w = 1 ∨ w = (z : E)) := fun w => by
    constructor
    · intro hw
      rcases hZ12 ⟨w, hw⟩ with h | h
      · exact Or.inl (congrArg Subtype.val h)
      · exact Or.inr (congrArg Subtype.val h)
    · rintro (rfl | rfl)
      · exact Z.one_mem
      · exact z.2
  refine ⟨π, z, ?_, hcen⟩
  exact
    { surjective := e.surjective.comp (QuotientGroup.mk'_surjective Z)
      perfect := ⟨hq.1⟩
      ne_one := fun h => hz1 (Subtype.ext h)
      sq_eq_one := by
        have h2 : z ^ 2 = 1 := by
          have := pow_card_eq_one' (G := Z) (x := z)
          rwa [hc] at this
        have h3 : (z : E) ^ 2 = 1 := by
          have := congrArg Subtype.val h2
          simpa using this
        rwa [pow_two] at h3
      central := fun x => by
        have := Subgroup.mem_center_iff.mp z.2 x
        exact this
      ker_iff := fun w => (hker w).trans (hcen w) }

@[expose] noncomputable def conjOn (K : Subgroup G) (u : G)
    (hu : u ∈ Subgroup.normalizer (K : Set G)) : MulAut ↥K where
  toFun x := ⟨u * x * u⁻¹, (Subgroup.mem_normalizer_iff.mp hu x).mp x.2⟩
  invFun x := ⟨u⁻¹ * x * u, by
    have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (K : Set G)).inv_mem hu) x).mp x.2
    simpa using this⟩
  left_inv x := Subtype.ext (by simp [mul_assoc])
  right_inv x := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

theorem conjOn_apply (K : Subgroup G) (u : G) (hu : u ∈ Subgroup.normalizer (K : Set G))
    (x : ↥K) : ((conjOn K u hu x : ↥K) : G) = u * x * u⁻¹ := rfl

theorem conjOn_mul_self (K : Subgroup G) {u : G} (hu : u ∈ Subgroup.normalizer (K : Set G))
    (hu2 : u * u = 1) : conjOn K u hu * conjOn K u hu = 1 := by
  ext x
  simp only [MulAut.mul_apply, MulAut.one_apply]
  show u * (u * (x : G) * u⁻¹) * u⁻¹ = x
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  rw [hui]
  calc u * (u * (x : G) * u) * u = (u * u) * (x : G) * (u * u) := by group
    _ = x := by rw [hu2]; group

@[expose] noncomputable def oddQuotAut (K : Subgroup G) (α : MulAut ↥K) : MulAut (OddQuot K) :=
  QuotientGroup.congr (classicalInvolutionOddCore ↥K) (classicalInvolutionOddCore ↥K) α
    (CFSG.ComponentClassification.OddCore.char_invariant α)

theorem oddQuotAut_mk (K : Subgroup G) (α : MulAut ↥K) (x : ↥K) :
    oddQuotAut K α (x : OddQuot K) = ((α x : ↥K) : OddQuot K) := rfl

theorem oddQuotAut_mul_self (K : Subgroup G) {α : MulAut ↥K} (hα : α * α = 1) :
    oddQuotAut K α * oddQuotAut K α = 1 := by
  ext q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  simp only [MulAut.mul_apply, MulAut.one_apply]
  rw [oddQuotAut_mk, oddQuotAut_mk]
  have : α (α x) = x := by
    have := congrArg (fun β : MulAut ↥K => β x) hα
    simpa using this
  rw [this]

theorem conjOn_one (K : Subgroup G) : conjOn K 1 (Subgroup.one_mem _) = 1 := by
  ext x
  simp [conjOn_apply]

theorem conjOn_mul (K : Subgroup G) {u v : G} (hu : u ∈ Subgroup.normalizer (K : Set G))
    (hv : v ∈ Subgroup.normalizer (K : Set G)) :
    conjOn K (u * v) ((Subgroup.normalizer (K : Set G)).mul_mem hu hv) =
      conjOn K u hu * conjOn K v hv := by
  ext x
  simp [conjOn_apply, mul_assoc]

theorem oddQuotAut_one (K : Subgroup G) : oddQuotAut K 1 = 1 := by
  ext q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  rfl

theorem oddQuotAut_mul (K : Subgroup G) (α β : MulAut ↥K) :
    oddQuotAut K (α * β) = oddQuotAut K α * oddQuotAut K β := by
  ext q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  rfl

@[expose] noncomputable def actHom (K R : Subgroup G) (hR : R ≤ Subgroup.normalizer (K : Set G)) :
    R →* MulAut (OddQuot K) where
  toFun r := oddQuotAut K (conjOn K r (hR r.2))
  map_one' := by
    show oddQuotAut K (conjOn K 1 (hR (Subgroup.one_mem R))) = 1
    rw [conjOn_one, oddQuotAut_one]
  map_mul' r s := by
    show oddQuotAut K (conjOn K (r * s : R) (hR (R.mul_mem r.2 s.2))) =
      oddQuotAut K (conjOn K r (hR r.2)) * oddQuotAut K (conjOn K s (hR s.2))
    rw [← oddQuotAut_mul, ← conjOn_mul]
    rfl

theorem centralizes_of_oddQuotAut_eq_one (hperf : Group.IsPerfect ↥K)
    (hP1 : classicalInvolutionOddCore ↥K ≤ Subgroup.center ↥K) {z : G}
    (hz : z ∈ Subgroup.normalizer (K : Set G)) (h : oddQuotAut K (conjOn K z hz) = 1) :
    ∀ k ∈ K, k * z = z * k := by
  refine centralizes_of_perfect_of_commutator_mem hperf hz
    (N := (classicalInvolutionOddCore ↥K).map K.subtype) ?_ ?_
  · rintro _ ⟨o, ho, rfl⟩ l hl
    have := Subgroup.mem_center_iff.mp (hP1 ho) ⟨l, hl⟩
    exact congrArg Subtype.val this.symm
  · intro k hk
    set x : ↥K := (⟨k, hk⟩ : ↥K)⁻¹ with hxdef
    have hx : x⁻¹ * conjOn K z hz x ∈ classicalInvolutionOddCore ↥K := by
      have h1 : oddQuotAut K (conjOn K z hz) (x : OddQuot K) = (x : OddQuot K) := by
        rw [h]; rfl
      rw [oddQuotAut_mk] at h1
      exact QuotientGroup.eq.mp h1.symm
    refine ⟨_, hx, ?_⟩
    show ((x⁻¹ * conjOn K z hz x : ↥K) : G) = k * z * k⁻¹ * z⁻¹
    simp [hxdef, conjOn_apply, mul_assoc]

end Witness

section WitnessFinite

variable {G : Type*} [Group G] [Finite G] {K : Subgroup G}

theorem odd_card_oddCore (K : Subgroup G) : Odd (Nat.card (classicalInvolutionOddCore ↥K)) :=
  CFSG.ComponentClassification.OddCore.odd_card ↥K

theorem unique_involution_of_witness (hw : A7Witness K) {z : G} (hz : orderOf z = 2)
    (hzK : z ∈ K) (hzc : ∀ k ∈ K, k * z = z * k) :
    ∀ w ∈ K, orderOf w = 2 → w = z := by
  obtain ⟨π, zE, hcov, hcen⟩ := exists_cover_of_witness hw
  set N : Subgroup ↥K := classicalInvolutionOddCore ↥K with hNdef
  have hN : Odd (Nat.card N) := odd_card_oddCore K
  let z' : ↥K := ⟨z, hzK⟩
  have hz'ord : orderOf z' = 2 := by rw [Subgroup.orderOf_mk]; exact hz
  have hz'2 : z' * z' = 1 := by
    have := pow_orderOf_eq_one z'
    rwa [hz'ord, pow_two] at this
  have hz'c : ∀ k : ↥K, k * z' = z' * k := fun k => Subtype.ext (hzc k k.2)
  have hz'N : z' ∉ N := by
    intro hzN
    have hdvd : orderOf (⟨z', hzN⟩ : N) ∣ Nat.card N := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, hz'ord] at hdvd
    exact absurd (hN.of_dvd_nat hdvd) (by decide)
  have hz'ne : (z' : OddQuot K) ≠ 1 := fun h => hz'N ((QuotientGroup.eq_one_iff z').mp h)
  have hz'cen : (z' : OddQuot K) ∈ Subgroup.center (OddQuot K) := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hz'c k]
  have hzEq : (z' : OddQuot K) = zE := by
    rcases (hcen _).mp hz'cen with h | h
    · exact absurd h hz'ne
    · exact h
  have hq : ∀ y : OddQuot K, y ≠ 1 → y * y = 1 → y = (z' : OddQuot K) := by
    intro y hy1 hy2
    rcases hcov.eq_one_or_eq_z_of_sq_eq_one hy2 with h | h
    · exact absurd h hy1
    · rw [hzEq]; exact h
  intro w hwK hw2
  have hw' : orderOf (⟨w, hwK⟩ : ↥K) = 2 := by rw [Subgroup.orderOf_mk]; exact hw2
  exact congrArg Subtype.val (unique_involution_of_central_of_quotient N hN hz'2 hz'c hq _ hw')

theorem exists_fixed_in_coset {α : MulAut ↥K} (hα : α * α = 1) (x₀ : ↥K)
    (hx₀ : oddQuotAut K α (x₀ : OddQuot K) = x₀) :
    ∃ x : ↥K, (x : OddQuot K) = x₀ ∧ α x = x := by
  classical
  set N : Subgroup ↥K := classicalInvolutionOddCore ↥K with hNdef
  have hαα : ∀ x : ↥K, α (α x) = x := fun x => by
    have := congrArg (fun β : MulAut ↥K => β x) hα
    simpa using this
  let C : Type _ := {x : ↥K // (x : OddQuot K) = x₀}
  have hmem : ∀ x : C, ((α x.1 : ↥K) : OddQuot K) = x₀ := fun x => by
    rw [← oddQuotAut_mk, x.2, hx₀]
  let σ : Equiv.Perm C :=
    { toFun := fun x => ⟨α x.1, hmem x⟩
      invFun := fun x => ⟨α x.1, hmem x⟩
      left_inv := fun x => Subtype.ext (hαα x.1)
      right_inv := fun x => Subtype.ext (hαα x.1) }
  have hσ : σ ^ 2 ^ 1 = 1 := by
    rw [pow_one, pow_two]
    apply Equiv.ext
    intro x
    apply Subtype.ext
    show α (α x.1) = x.1
    exact hαα x.1
  have hCN : Nat.card C = Nat.card N := by
    refine Nat.card_congr
      { toFun := fun x => ⟨x₀⁻¹ * x.1, QuotientGroup.eq.mp x.2.symm⟩
        invFun := fun n => ⟨x₀ * n.1, QuotientGroup.eq.mpr (by simp)⟩
        left_inv := fun x => Subtype.ext (by simp)
        right_inv := fun n => Subtype.ext (by simp) }
  have : Fintype C := Fintype.ofFinite C
  have hodd : ¬ 2 ∣ Fintype.card C := by
    rw [← Nat.card_eq_fintype_card, hCN]
    exact (odd_card_oddCore K).not_two_dvd_nat
  obtain ⟨a, ha⟩ := Equiv.Perm.exists_fixed_point_of_prime (p := 2) (n := 1) hodd hσ
  exact ⟨a.1, a.2, congrArg Subtype.val ha⟩

theorem exists_two_subgroup_centralizing (hw : A7Witness K) {u : G}
    (hu : u ∈ Subgroup.normalizer (K : Set G)) (hu2 : u * u = 1) :
    ∃ R : Subgroup G, R ≤ K ∧ IsPGroup 2 R ∧ 8 ≤ Nat.card R ∧ ∀ r ∈ R, u * r = r * u := by
  obtain ⟨π, z, hcov, -⟩ := exists_cover_of_witness hw
  set N : Subgroup ↥K := classicalInvolutionOddCore ↥K with hNdef
  set α : MulAut ↥K := conjOn K u hu with hαdef
  have hαα : α * α = 1 := conjOn_mul_self K hu hu2
  have hᾱ : oddQuotAut K α * oddQuotAut K α = 1 := oddQuotAut_mul_self K hαα
  obtain ⟨Rb, hRbp, hRb8, hRbfix⟩ := hcov.exists_fixed_two_subgroup (oddQuotAut K α) hᾱ
  let Rt : Subgroup ↥K := Rb.comap (QuotientGroup.mk' N)
  let F : Subgroup ↥K := fixedIn α Rt
  have hlift : ∀ r ∈ Rb, ∃ x ∈ F, (x : OddQuot K) = r := by
    intro r hr
    obtain ⟨x₀, rfl⟩ := QuotientGroup.mk_surjective r
    obtain ⟨x, hx, hαx⟩ := exists_fixed_in_coset hαα x₀ (hRbfix _ hr)
    exact ⟨x, ⟨by show (x : OddQuot K) ∈ Rb; rw [hx]; exact hr, hαx⟩, hx⟩
  let f : F →* OddQuot K := (QuotientGroup.mk' N).comp F.subtype
  have hfrange : f.range = Rb := by
    ext r
    constructor
    · rintro ⟨x, rfl⟩
      exact x.2.1
    · intro hr
      obtain ⟨x, hxF, hx⟩ := hlift r hr
      exact ⟨⟨x, hxF⟩, hx⟩
  have hcardRb : 8 ∣ Nat.card Rb := by
    obtain ⟨k, hk⟩ := hRbp.exists_card_eq
    rw [hk] at hRb8 ⊢
    have hk3 : 3 ≤ k := by
      by_contra hlt
      have : k ≤ 2 := by omega
      have : 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) this
      omega
    exact (pow_dvd_pow 2 hk3 : 2 ^ 3 ∣ 2 ^ k)
  have hdvdF : Nat.card Rb ∣ Nat.card F := by
    have h1 := Subgroup.card_ker_mul_card_range f
    rw [hfrange] at h1
    exact Dvd.intro_left _ h1
  have h8F : 2 ^ 3 ∣ Nat.card F := (by norm_num : (2 : ℕ) ^ 3 = 8) ▸ hcardRb.trans hdvdF
  obtain ⟨B, hB⟩ := Sylow.exists_subgroup_card_pow_prime 2 h8F
  let R : Subgroup G := (B.map F.subtype).map K.subtype
  have hRcard : Nat.card R = 8 := by
    rw [Subgroup.card_map_of_injective K.subtype_injective,
      Subgroup.card_map_of_injective F.subtype_injective, hB]
    norm_num
  refine ⟨R, ?_, ?_, by omega, ?_⟩
  · rintro _ ⟨y, _, rfl⟩
    exact y.2
  · exact IsPGroup.of_card (n := 3) (by rw [hRcard]; norm_num)
  · rintro _ ⟨y, ⟨b, hb, rfl⟩, rfl⟩
    have hbF : (b : ↥K) ∈ F := b.2
    have hfix : α (b : ↥K) = b := hbF.2
    have h1 : u * ((b : ↥K) : G) * u⁻¹ = ((b : ↥K) : G) := congrArg Subtype.val hfix
    calc u * ((b : ↥K) : G) = u * ((b : ↥K) : G) * u⁻¹ * u := by group
      _ = ((b : ↥K) : G) * u := by rw [h1]

theorem oddQuotAut_conjOn_eq_one (hw : A7Witness K) (Q : Sylow 2 ↥K) {g : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G))
    (hQ : ∀ q ∈ (Q : Subgroup ↥K), g * (q : G) = (q : G) * g) :
    oddQuotAut K (conjOn K g hg) = 1 := by
  obtain ⟨π, z, hcov, -⟩ := exists_cover_of_witness hw
  have hf : Function.Surjective (QuotientGroup.mk' (classicalInvolutionOddCore ↥K)) :=
    QuotientGroup.mk'_surjective _
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply hcov.mulAut_eq_one_of_centralizes_sylow (Q.mapSurjective hf)
  intro x hx
  rw [Sylow.coe_mapSurjective] at hx
  obtain ⟨q, hq, rfl⟩ := hx
  show oddQuotAut K (conjOn K g hg) (q : OddQuot K) = (q : OddQuot K)
  rw [oddQuotAut_mk]
  congr 1
  apply Subtype.ext
  show g * (q : G) * g⁻¹ = q
  rw [hQ q hq]
  group

theorem commutator_mem_oddCore_of_centralizes_sylow (hw : A7Witness K) (Q : Sylow 2 ↥K) {g : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G))
    (hQ : ∀ q ∈ (Q : Subgroup ↥K), g * (q : G) = (q : G) * g) (k : ↥K) :
    k⁻¹ * conjOn K g hg k ∈ classicalInvolutionOddCore ↥K := by
  have h := oddQuotAut_conjOn_eq_one hw Q hg hQ
  have h1 : oddQuotAut K (conjOn K g hg) (k : OddQuot K) = (k : OddQuot K) := by
    rw [h]; rfl
  rw [oddQuotAut_mk] at h1
  exact QuotientGroup.eq.mp h1.symm

theorem oddQuotAut_conjOn_eq_one_of_card (hw : A7Witness K) {R : Subgroup G}
    (hR : R ≤ Subgroup.normalizer (K : Set G)) (h2 : IsPGroup 2 R) {z : G} (hzR : z ∈ R)
    (huniq : ∀ x ∈ R, orderOf x = 2 → x = z) (hcard : 4 < Nat.card R) :
    oddQuotAut K (conjOn K z (hR hzR)) = 1 := by
  obtain ⟨π, zE, hcov, -⟩ := exists_cover_of_witness hw
  have hz2 : ∀ x : R, orderOf x = 2 → x = ⟨z, hzR⟩ := fun x hx =>
    Subtype.ext (huniq x x.2 (by rw [← hx, Subgroup.orderOf_coe]))
  have := involution_acts_trivially_of_four_lt_card h2 hz2 (actHom K R hR) hcov.autPerm
    hcov.autPerm_injective hcard
  exact this

end WitnessFinite

end CFSG.ClassicalInvolution.Hat2A7
