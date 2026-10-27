module

public import CFSG.GH74.QTGen4.Recog.G23.HLetters
public import CFSG.GH74.QTGen4.Recog.G23.P7.OpenLeaves

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Recog.G23.P7

open CFSG.Open CFSG.Quasithin.G23Type CFSG.GH74.QTGen4.Recog.G23 CFSG.CosetTable

variable {G : Type} [Group G]

open scoped MatrixGroups

def hrI : SL(2, ZMod 3) := ⟨!![0, 1; 2, 0], by decide +kernel⟩

def hrJ : SL(2, ZMod 3) := ⟨!![1, 1; 1, 2], by decide +kernel⟩

def hrJi : SL(2, ZMod 3) := ⟨!![2, 2; 2, 1], by decide +kernel⟩

theorem hr_pow4_mul_M2 : ∀ X Y : M2, X.det = 1 → Y.det = 1 → X ^ 4 = 1 → Y ^ 4 = 1 →
    (X * Y) ^ 4 = 1 := by
  decide +kernel

theorem hr_pow4_mul (A B : SL(2, ZMod 3)) (hA : A ^ 4 = 1) (hB : B ^ 4 = 1) :
    (A * B) ^ 4 = 1 := by
  have h4 : ∀ C : SL(2, ZMod 3), C ^ 4 = 1 → C.1 ^ 4 = 1 := by
    intro C hC
    have := congrArg Subtype.val hC
    rwa [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one] at this
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_one]
  exact hr_pow4_mul_M2 A.1 B.1 A.2 B.2 (h4 A hA) (h4 B hB)

theorem hr_I_pow4 : hrI ^ 4 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
  decide +kernel

theorem hr_J_pow4 : hrJ ^ 4 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
  decide +kernel

theorem hr_I_sq_ne : hrI * hrI ≠ 1 := by
  have hne : hrI.1 * hrI.1 ≠ 1 := by decide +kernel
  intro h
  apply hne
  have := congrArg Subtype.val h
  rwa [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] at this

theorem hr_J_sq_ne : hrJ * hrJ ≠ 1 := by
  have hne : hrJ.1 * hrJ.1 ≠ 1 := by decide +kernel
  intro h
  apply hne
  have := congrArg Subtype.val h
  rwa [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] at this

theorem hr_J_inv : hrJ * hrJi = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  decide +kernel

theorem hr_J_inv_eq : hrJ⁻¹ = hrJi := inv_eq_of_mul_eq_one_right hr_J_inv

theorem hr_fin : (hrI * hrJi) ^ 2 ≠ 1 := by
  have hne : (hrI.1 * hrJi.1) ^ 2 ≠ 1 := by decide +kernel
  intro h
  apply hne
  have := congrArg Subtype.val h
  rwa [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_one] at this

def hrQ8 {K : Subgroup G} (ψ : ↥K ≃* SL(2, ZMod 3)) : Subgroup G where
  carrier := {g | g ∈ K ∧ g ^ 4 = 1}
  mul_mem' := by
    rintro g h ⟨hg, hg4⟩ ⟨hh, hh4⟩
    have key : ∀ x : ↥K, (x : G) ^ 4 = 1 → ψ x ^ 4 = 1 := by
      intro x hx
      have hx' : x ^ 4 = 1 := Subtype.ext (by simpa using hx)
      rw [← map_pow, hx', map_one]
    have h1 := hr_pow4_mul (ψ ⟨g, hg⟩) (ψ ⟨h, hh⟩) (key ⟨g, hg⟩ hg4) (key ⟨h, hh⟩ hh4)
    rw [← map_mul, ← map_pow] at h1
    have h2 : (⟨g, hg⟩ * ⟨h, hh⟩ : ↥K) ^ 4 = 1 := ψ.injective (by rw [map_one]; exact h1)
    show g * h ∈ K ∧ (g * h) ^ 4 = 1
    exact ⟨K.mul_mem hg hh, by simpa using congrArg Subtype.val h2⟩
  one_mem' := by
    show (1 : G) ∈ K ∧ (1 : G) ^ 4 = 1
    exact ⟨K.one_mem, by simp⟩
  inv_mem' := by
    rintro g ⟨hg, hg4⟩
    show g⁻¹ ∈ K ∧ g⁻¹ ^ 4 = 1
    exact ⟨K.inv_mem hg, by rw [inv_pow, hg4, inv_one]⟩

theorem mem_hrQ8 {K : Subgroup G} (ψ : ↥K ≃* SL(2, ZMod 3)) {g : G} :
    g ∈ hrQ8 ψ ↔ g ∈ K ∧ g ^ 4 = 1 := Iff.rfl

theorem hr_q8_normal {H K : Subgroup G} (hH : H ≤ Subgroup.normalizer (K : Set G))
    (ψ : ↥K ≃* SL(2, ZMod 3)) : ((hrQ8 ψ).subgroupOf H).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  obtain ⟨hn1, hn4⟩ := (mem_hrQ8 ψ).mp hn
  show (g : G) * (n : G) * (g : G)⁻¹ ∈ hrQ8 ψ
  refine (mem_hrQ8 ψ).mpr ⟨(Subgroup.mem_normalizer_iff.mp (hH g.2) n).mp hn1, ?_⟩
  rw [conj_pow, hn4, mul_one, mul_inv_cancel]

theorem hr_q8_isPGroup {K : Subgroup G} (ψ : ↥K ≃* SL(2, ZMod 3)) : IsPGroup 2 (hrQ8 ψ) := by
  intro x
  refine ⟨2, Subtype.ext ?_⟩
  have hx : (x : G) ^ 4 = 1 := ((mem_hrQ8 ψ).mp x.2).2
  simpa using hx

theorem hr_le_of_normal_two {T H N : Subgroup G} (hT : quasithinIsSylowTwo T)
    (hTH : T ≤ H) (hNH : N ≤ H) (hN : (N.subgroupOf H).Normal) (hN2 : IsPGroup 2 N) :
    N ≤ T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT' : IsPGroup 2 T ∧ ¬ 2 ∣ T.index := hT
  have hTsub : IsPGroup 2 (T.subgroupOf H) :=
    hT'.1.of_injective (Subgroup.subgroupOfEquivOfLe hTH).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hTH).injective
  have hTdvd : (T.subgroupOf H).index ∣ T.index := Dvd.intro _ (Subgroup.relIndex_mul_index hTH)
  have hTidx : ¬ 2 ∣ (T.subgroupOf H).index := fun h => hT'.2 (dvd_trans h hTdvd)
  have hNsub : IsPGroup 2 (N.subgroupOf H) :=
    hN2.of_injective (Subgroup.subgroupOfEquivOfLe hNH).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hNH).injective
  have hle := IsPGroup.le_sylow_of_normal hNsub (hTsub.toSylow hTidx)
  rw [IsPGroup.toSylow_coe] at hle
  intro n hn
  have hx : (⟨n, hNH hn⟩ : ↥H) ∈ N.subgroupOf H := Subgroup.mem_subgroupOf.mpr hn
  exact Subgroup.mem_subgroupOf.mp (hle hx)

theorem hr_sq_eq {K : Subgroup G} {z : G} (ψ : ↥K ≃* SL(2, ZMod 3)) (hzK : z ∈ K)
    (hz2 : z ^ 2 = 1) (hz1 : z ≠ 1) (a : ↥K) (ha4 : (a : G) ^ 4 = 1)
    (hs : ψ a * ψ a ≠ 1) (hzψ : ψ ⟨z, hzK⟩ = slZ) : (a : G) * a = z := by
  have hy : (a : G) * a ∈ K := K.mul_mem a.2 a.2
  have hy2 : ((a : G) * a) ^ 2 = 1 := by
    rw [pow_two]
    calc (a : G) * a * ((a : G) * a) = (a : G) ^ 4 := by
          rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
      _ = 1 := ha4
  have hy1 : (a : G) * a ≠ 1 := by
    intro h
    apply hs
    have h' : a * a = 1 := Subtype.ext h
    rw [← map_mul, h', map_one]
  have h4 : ψ ⟨(a : G) * a, hy⟩ = ψ ⟨z, hzK⟩ := by
    rw [invol_eq_slZ ψ hy hy2 hy1, hzψ]
  exact congrArg Subtype.val (ψ.injective h4)

theorem leafHR
    : LeafHR := by
  intro G _ _ T H H₁ H₂ M hctx
  obtain ⟨ψ₁⟩ := hctx.one.iso_one
  obtain ⟨ψ₂⟩ := hctx.one.iso_two
  obtain ⟨z, hzI, hz1, -⟩ := G23One.exists_unique_inf hctx.one
  have hz2 : z ^ 2 = 1 := G23One.sq_inf hctx.one hzI
  have hzH₁ : z ∈ H₁ := (Subgroup.mem_inf.mp hzI).1
  have hzH₂ : z ∈ H₂ := (Subgroup.mem_inf.mp hzI).2
  have hzA : ψ₁ ⟨z, hzH₁⟩ = slZ := invol_eq_slZ ψ₁ hzH₁ hz2 hz1
  have hzB : ψ₂ ⟨z, hzH₂⟩ = slZ := invol_eq_slZ ψ₂ hzH₂ hz2 hz1
  have hQ₁T : hrQ8 ψ₁ ≤ T :=
    hr_le_of_normal_two hctx.sylow hctx.tH
      (fun g hg => hctx.one.le_one ((mem_hrQ8 ψ₁).mp hg).1)
      (hr_q8_normal hctx.one.normal_one ψ₁) (hr_q8_isPGroup ψ₁)
  have hQ₂T : hrQ8 ψ₂ ≤ T :=
    hr_le_of_normal_two hctx.sylow hctx.tH
      (fun g hg => hctx.one.le_two ((mem_hrQ8 ψ₂).mp hg).1)
      (hr_q8_normal hctx.one.normal_two ψ₂) (hr_q8_isPGroup ψ₂)
  obtain ⟨a, ha₁⟩ : ∃ a : ↥H₁, ψ₁ a = hrI := ⟨ψ₁.symm hrI, ψ₁.apply_symm_apply _⟩
  obtain ⟨a', ha'₁⟩ : ∃ a' : ↥H₁, ψ₁ a' = hrJ := ⟨ψ₁.symm hrJ, ψ₁.apply_symm_apply _⟩
  obtain ⟨b, hb₂⟩ : ∃ b : ↥H₂, ψ₂ b = hrI := ⟨ψ₂.symm hrI, ψ₂.apply_symm_apply _⟩
  have ha4 : (a : G) ^ 4 = 1 := by
    have h : a ^ 4 = 1 := ψ₁.injective (by rw [map_pow, ha₁, map_one]; exact hr_I_pow4)
    simpa using congrArg Subtype.val h
  have ha'4 : (a' : G) ^ 4 = 1 := by
    have h : a' ^ 4 = 1 := ψ₁.injective (by rw [map_pow, ha'₁, map_one]; exact hr_J_pow4)
    simpa using congrArg Subtype.val h
  have hb4 : (b : G) ^ 4 = 1 := by
    have h : b ^ 4 = 1 := ψ₂.injective (by rw [map_pow, hb₂, map_one]; exact hr_I_pow4)
    simpa using congrArg Subtype.val h
  have haa : (a : G) * a = z :=
    hr_sq_eq ψ₁ hzH₁ hz2 hz1 a ha4 (by rw [ha₁]; exact hr_I_sq_ne) hzA
  have ha'a' : (a' : G) * a' = z :=
    hr_sq_eq ψ₁ hzH₁ hz2 hz1 a' ha'4 (by rw [ha'₁]; exact hr_J_sq_ne) hzA
  have hbb : (b : G) * b = z :=
    hr_sq_eq ψ₂ hzH₂ hz2 hz1 b hb4 (by rw [hb₂]; exact hr_I_sq_ne) hzB
  have hcab : (a : G) * b = b * a := G23One.comm_one_two hctx.one a.2 b.2
  have hca'b : (a' : G) * b = b * a' := G23One.comm_one_two hctx.one a'.2 b.2
  have hx1 : ((a : G) * b) * ((a : G) * b) = 1 := by
    calc ((a : G) * b) * ((a : G) * b) = (a : G) * ((b : G) * a) * b := by group
      _ = (a : G) * ((a : G) * b) * b := by rw [← hcab]
      _ = ((a : G) * a) * ((b : G) * b) := by group
      _ = z * z := by rw [haa, hbb]
      _ = 1 := by rw [← pow_two, hz2]
  have hx2 : ((a' : G) * b) * ((a' : G) * b) = 1 := by
    calc ((a' : G) * b) * ((a' : G) * b) = (a' : G) * ((b : G) * a') * b := by group
      _ = (a' : G) * ((a' : G) * b) * b := by rw [← hca'b]
      _ = ((a' : G) * a') * ((b : G) * b) := by group
      _ = z * z := by rw [ha'a', hbb]
      _ = 1 := by rw [← pow_two, hz2]
  have hM1 : (a : G) * b ∈ M :=
    M.mul_mem (hctx.tM (hQ₁T ((mem_hrQ8 ψ₁).mpr ⟨a.2, ha4⟩)))
      (hctx.tM (hQ₂T ((mem_hrQ8 ψ₂).mpr ⟨b.2, hb4⟩)))
  have hM2 : (a' : G) * b ∈ M :=
    M.mul_mem (hctx.tM (hQ₁T ((mem_hrQ8 ψ₁).mpr ⟨a'.2, ha'4⟩)))
      (hctx.tM (hQ₂T ((mem_hrQ8 ψ₂).mpr ⟨b.2, hb4⟩)))
  by_cases h1 : (a : G) * b ∈ quasithinGenFitting M
  · by_cases h2 : (a' : G) * b ∈ quasithinGenFitting M
    · exfalso
      have hwG : ((a * a'⁻¹ : ↥H₁) : G) = ((a : G) * b) * ((a' : G) * b)⁻¹ := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      have hwV : ((a * a'⁻¹ : ↥H₁) : G) ∈ quasithinGenFitting M := by
        rw [hwG]
        exact (quasithinGenFitting M).mul_mem h1 ((quasithinGenFitting M).inv_mem h2)
      have hw2 : ((a * a'⁻¹ : ↥H₁) : G) ^ 2 = 1 := hctx.two.elem.2 _ hwV
      have hw2' : (a * a'⁻¹ : ↥H₁) ^ 2 = 1 := Subtype.ext (by simpa using hw2)
      have hψ : ψ₁ (a * a'⁻¹) = hrI * hrJi := by
        rw [map_mul, map_inv, ha₁, ha'₁, hr_J_inv_eq]
      have h3 := congrArg ψ₁ hw2'
      rw [map_pow, hψ, map_one] at h3
      exact hr_fin h3
    · exact ⟨(a' : G) * b, hM2, hx2, h2⟩
  · exact ⟨(a : G) * b, hM1, hx1, h1⟩

end CFSG.GH74.QTGen4.Recog.G23.P7
