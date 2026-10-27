module

public import CFSG.ClassicalInvolution.Uniform.U4Wiel1
public import CFSG.ClassicalInvolution.Uniform.U4Twin

public section

namespace CFSG.ClassicalInvolution.Uniform.U4

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Hat2A7
open CFSG.ComponentClassification
open scoped commutatorElement MatrixGroups

variable {F : Type} [Group F] [Finite F]

theorem exists_fixed_coset {N : Subgroup F} (hNodd : Odd (Nat.card N)) {x j : F}
    (hx2 : x * x = 1) (hxN : ∀ n ∈ N, x * n * x⁻¹ ∈ N) (hjN : ∀ n ∈ N, j⁻¹ * n * j ∈ N)
    (hc : x * j * x⁻¹ * j⁻¹ ∈ N) : ∃ c : F, x * c = c * x ∧ j⁻¹ * c ∈ N := by
  classical
  set c₀ : F := j⁻¹ * x * j * x⁻¹ with hc₀
  have hc₀N : c₀ ∈ N := by
    have := hjN _ hc
    have e : j⁻¹ * (x * j * x⁻¹ * j⁻¹) * j = c₀ := by rw [hc₀]; group
    rwa [e] at this
  have hxi : x⁻¹ * x⁻¹ = 1 := by rw [← mul_inv_rev, hx2, inv_one]
  have hxx : ∀ a : F, x * (x * a * x⁻¹) * x⁻¹ = a := by
    intro a
    calc x * (x * a * x⁻¹) * x⁻¹ = (x * x) * a * (x⁻¹ * x⁻¹) := by group
      _ = a := by rw [hx2, hxi]; group
  have hc₀c : c₀ * (x * c₀ * x⁻¹) = 1 := by
    calc c₀ * (x * c₀ * x⁻¹) = j⁻¹ * (x * x) * j * (x⁻¹ * x⁻¹) := by rw [hc₀]; group
      _ = 1 := by rw [hx2, hxi]; group
  let f : N → N := fun n => ⟨c₀ * (x * n * x⁻¹), N.mul_mem hc₀N (hxN n n.2)⟩
  have hf : Function.Involutive f := by
    intro n
    apply Subtype.ext
    show c₀ * (x * (c₀ * (x * (n : F) * x⁻¹)) * x⁻¹) = n
    calc c₀ * (x * (c₀ * (x * (n : F) * x⁻¹)) * x⁻¹)
        = (c₀ * (x * c₀ * x⁻¹)) * (x * (x * (n : F) * x⁻¹) * x⁻¹) := by group
      _ = n := by rw [hc₀c, hxx, one_mul]
  let σ : Equiv.Perm N := hf.toPerm f
  have hσ : σ ^ 2 ^ 1 = 1 := by
    ext n
    simp [pow_two, σ, hf n]
  have : Fintype N := Fintype.ofFinite N
  have hodd : ¬ 2 ∣ Fintype.card N := by
    rw [← Nat.card_eq_fintype_card]
    intro h
    exact (Nat.not_even_iff_odd.mpr hNodd) (even_iff_two_dvd.mpr h)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n₀, hn₀⟩ := Equiv.Perm.exists_fixed_point_of_prime (p := 2) (n := 1) hodd hσ
  have hfix : c₀ * (x * (n₀ : F) * x⁻¹) = n₀ := congrArg Subtype.val hn₀
  refine ⟨j * n₀, ?_, by simp⟩
  calc x * (j * n₀) = (x * j * x⁻¹) * (x * (n₀ : F) * x⁻¹) * x := by group
    _ = (j * c₀) * (x * (n₀ : F) * x⁻¹) * x := by
        rw [show x * j * x⁻¹ = j * c₀ from by rw [hc₀]; group]
    _ = j * (c₀ * (x * (n₀ : F) * x⁻¹)) * x := by group
    _ = j * n₀ * x := by rw [hfix]

theorem exists_mem_inf_centralizer_of_trivial {J : Subgroup F} {x : F} (hx2 : x * x = 1)
    (hxJ : x ∈ Subgroup.normalizer (J : Set F)) (hζ : ∀ j ∈ J, ⁅x, j⁆ ∈ oddCoreOf J) :
    ∀ j ∈ J, ∃ c ∈ J ⊓ Subgroup.centralizer ({x} : Set F), c⁻¹ * j ∈ oddCoreOf J := by
  intro j hj
  have hxN : ∀ n ∈ oddCoreOf J, x * n * x⁻¹ ∈ oddCoreOf J := fun n hn =>
    mem_normalizer_oddCoreOf_of_mem_normalizer hxJ hn
  have hjN : ∀ n ∈ oddCoreOf J, j⁻¹ * n * j ∈ oddCoreOf J := fun n hn => by
    have := mem_normalizer_oddCoreOf_of_mem_normalizer
      ((Subgroup.normalizer (J : Set F)).inv_mem (Subgroup.le_normalizer hj)) hn
    simpa using this
  have hc : x * j * x⁻¹ * j⁻¹ ∈ oddCoreOf J := by
    have := hζ j hj
    rwa [commutatorElement_def] at this
  obtain ⟨c, hxc, hcN⟩ := exists_fixed_coset (oddCoreOf_odd_natCard J) hx2 hxN hjN hc
  have hcJ : c ∈ J := by
    have h1 : j * (j⁻¹ * c) ∈ J := J.mul_mem hj (oddCoreOf_le_self J hcN)
    simpa using h1
  refine ⟨c, ⟨hcJ, Subgroup.mem_centralizer_singleton_iff.mpr hxc.symm⟩, ?_⟩
  have := (oddCoreOf J).inv_mem hcN
  simpa using this

theorem nonempty_quotEquiv_of_cover {A B : Subgroup F} (hAB : A ≤ B)
    (hcov : ∀ b ∈ B, ∃ a ∈ A, a⁻¹ * b ∈ oddCoreOf B) {T : Type*} [Group T]
    (e : ↥B ⧸ classicalInvolutionOddCore ↥B ≃* T) :
    Nonempty (↥A ⧸ classicalInvolutionOddCore ↥A ≃* T) := by
  classical
  have hoddA : Odd (Nat.card ↥(classicalInvolutionOddCore ↥A)) := OddCore.odd_card ↥A
  have hoddB : Odd (Nat.card ↥(classicalInvolutionOddCore ↥B)) := OddCore.odd_card ↥B
  have hcf : componentClassificationOddCore (↥B ⧸ classicalInvolutionOddCore ↥B) = ⊥ :=
    OddCore.quotient_corefree ↥B
  let φ : ↥A →* ↥B ⧸ classicalInvolutionOddCore ↥B :=
    (QuotientGroup.mk' (classicalInvolutionOddCore ↥B)).comp (Subgroup.inclusion hAB)
  have hφs : Function.Surjective φ := by
    intro q
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨a, haA, ha⟩ := hcov b b.2
    obtain ⟨hmem, hmemNB⟩ := mem_oddCoreOf_iff.mp ha
    refine ⟨⟨a, haA⟩, ?_⟩
    show (QuotientGroup.mk (Subgroup.inclusion hAB ⟨a, haA⟩) :
      ↥B ⧸ classicalInvolutionOddCore ↥B) = QuotientGroup.mk b
    rw [QuotientGroup.eq]
    exact hmemNB
  have hker : φ.ker = classicalInvolutionOddCore ↥A := by
    apply le_antisymm
    ·
      have hnorm : (φ.ker).Normal := MonoidHom.normal_ker φ
      have hle : φ.ker.map (Subgroup.inclusion hAB) ≤ classicalInvolutionOddCore ↥B := by
        rintro _ ⟨x, hx, rfl⟩
        have : φ x = 1 := hx
        exact (QuotientGroup.eq_one_iff _).mp this
      have hdvd : Nat.card φ.ker ∣ Nat.card ↥(classicalInvolutionOddCore ↥B) := by
        have h1 := Subgroup.card_dvd_of_le hle
        rwa [Subgroup.card_map_of_injective (Subgroup.inclusion_injective hAB)] at h1
      exact OddCore.maximal ↥A φ.ker hnorm (hoddB.of_dvd_nat hdvd)
    · intro x hx
      have hcore : (classicalInvolutionOddCore ↥A).map φ ≤
          componentClassificationOddCore (↥B ⧸ classicalInvolutionOddCore ↥B) :=
        OddCore.maximal _ _ (Subgroup.Normal.map inferInstance φ hφs)
          (hoddA.of_dvd_nat (Subgroup.card_map_dvd (H := classicalInvolutionOddCore ↥A) φ))
      rw [hcf] at hcore
      have : φ x ∈ (⊥ : Subgroup (↥B ⧸ classicalInvolutionOddCore ↥B)) :=
        hcore (Subgroup.mem_map_of_mem φ hx)
      exact this
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hφs)).trans e⟩

theorem commutator_inf_le_oddCoreIn {K J : Subgroup F} {z t : F} (hK : Mem3 K z) (hJ : Mem3 J t)
    (hne : t ≠ z) (hzJ : z ∈ Subgroup.normalizer (J : Set F))
    (htK : t ∈ Subgroup.normalizer (K : Set F)) (hzt : z * t = t * z)
    (hζ : ∀ j ∈ J, ⁅z, j⁆ ∈ oddCoreOf J) (hτ : ∀ k ∈ K, ⁅t, k⁆ ∈ oddCoreOf K) :
    ⁅K ⊓ Subgroup.centralizer ({t} : Set F), J ⊓ Subgroup.centralizer ({z} : Set F)⁆ ≤
      Balance.oddCoreIn
        (Subgroup.centralizer ({t} : Set F) ⊓ Subgroup.centralizer ({z} : Set F)) := by
  have hz2 : orderOf z = 2 := hK.orderOf_eq_two
  have ht2 : orderOf t = 2 := hJ.orderOf_eq_two
  have hzz : z * z = 1 := hK.mul_self
  have htt : t * t = 1 := hJ.mul_self
  have eJ := nonempty_quotEquiv_of_cover (A := J ⊓ Subgroup.centralizer ({z} : Set F)) (B := J)
    inf_le_left (exists_mem_inf_centralizer_of_trivial hzz hzJ hζ) hJ.equiv
  have eK := nonempty_quotEquiv_of_cover (A := K ⊓ Subgroup.centralizer ({t} : Set F)) (B := K)
    inf_le_left (exists_mem_inf_centralizer_of_trivial htt htK hτ) hK.equiv
  have hJsub : IsSubnormal (J ⊓ Subgroup.centralizer ({z} : Set F))
      (Subgroup.centralizer ({t} : Set F) ⊓ Subgroup.centralizer ({z} : Set F)) :=
    isSubnormal_inf hJ.subnormal _
  have hKsub : IsSubnormal (K ⊓ Subgroup.centralizer ({t} : Set F))
      (Subgroup.centralizer ({t} : Set F) ⊓ Subgroup.centralizer ({z} : Set F)) := by
    have := isSubnormal_inf hK.subnormal (Subgroup.centralizer ({t} : Set F))
    rwa [inf_comm (Subgroup.centralizer ({z} : Set F))] at this
  refine commutator_le_oddCoreIn_central hKsub hJsub hz2 ?_ ht2 ?_ hzt (Ne.symm hne) ?_ eK eJ
  · exact ⟨hK.mem, Subgroup.mem_centralizer_singleton_iff.mpr hzt⟩
  · exact ⟨hJ.mem, Subgroup.mem_centralizer_singleton_iff.mpr hzt.symm⟩
  · intro y hy
    exact (Subgroup.mem_centralizer_singleton_iff.mp hy.1).symm

theorem false_of_trivBoth {K J : Subgroup F} {z t : F} (hK : Mem3 K z) (hJ : Mem3 J t)
    (hne : t ≠ z) {v : F} (hvJ : v ∈ J) (hvv : v * v = t) (hvz : v * z = z * v)
    (hzJ : z ∈ Subgroup.normalizer (J : Set F)) (hvK : v * v ∈ Subgroup.normalizer (K : Set F))
    (hv : v ∉ Subgroup.normalizer (K : Set F)) (hζ : ∀ j ∈ J, ⁅z, j⁆ ∈ oddCoreOf J)
    (hτ : ∀ k ∈ K, ⁅v * v, k⁆ ∈ oddCoreOf K) {R : Subgroup F} (hR2 : IsPGroup 2 R) {a₀ : F}
    (ha₀ : a₀ ∈ R ⊓ K) (hRinv : ∀ q ∈ R ⊓ K, v⁻¹ * q * v ∈ R ⊓ conjSub v⁻¹ K)
    (ha₀2 : a₀ * a₀ = z) (hta₀ : t * a₀ = a₀ * t) : False := by
  have hz2 : z * z = 1 := hK.mul_self
  have htK : t ∈ Subgroup.normalizer (K : Set F) := hvv ▸ hvK
  have hzt : z * t = t * z := by
    rw [← hvv]
    calc z * (v * v) = (z * v) * v := by group
      _ = (v * z) * v := by rw [hvz]
      _ = v * (z * v) := by group
      _ = v * (v * z) := by rw [hvz]
      _ = (v * v) * z := by group
  have hτ' : ∀ k ∈ K, ⁅t, k⁆ ∈ oddCoreOf K := fun k hk => by
    rw [← hvv]
    exact hτ k hk
  have hcomm := commutator_inf_le_oddCoreIn hK hJ hne hzJ htK hzt hζ hτ'
  have hv'Jx : v⁻¹ ∈ J ⊓ Subgroup.centralizer ({z} : Set F) :=
    ⟨J.inv_mem hvJ, Subgroup.mem_centralizer_singleton_iff.mpr (inv_comm_of_comm hvz)⟩
  have ha₀Kx : a₀ ∈ K ⊓ Subgroup.centralizer ({t} : Set F) :=
    ⟨ha₀.2, Subgroup.mem_centralizer_singleton_iff.mpr hta₀.symm⟩
  have hu : ⁅a₀, v⁻¹⁆ ∈ Balance.oddCoreIn
      (Subgroup.centralizer ({t} : Set F) ⊓ Subgroup.centralizer ({z} : Set F)) :=
    hcomm (Subgroup.commutator_mem_commutator ha₀Kx hv'Jx)
  have hu' : v⁻¹ * a₀ * v * a₀⁻¹ ∈ Balance.oddCoreIn
      (Subgroup.centralizer ({t} : Set F) ⊓ Subgroup.centralizer ({z} : Set F)) := by
    have := (Balance.oddCoreIn
      (Subgroup.centralizer ({t} : Set F) ⊓ Subgroup.centralizer ({z} : Set F))).inv_mem hu
    rw [commutatorElement_inv] at this
    simpa [commutatorElement_def] using this
  have huR : v⁻¹ * a₀ * v * a₀⁻¹ ∈ R := R.mul_mem (hRinv a₀ ha₀).1 (R.inv_mem ha₀.1)
  have hu1 : v⁻¹ * a₀ * v * a₀⁻¹ = 1 :=
    eq_one_of_isPGroup_of_mem_odd (Balance.odd_card_oddCoreIn _) hu'
      (hR2.to_le (Subgroup.zpowers_le.mpr huR))
  have hfix : v⁻¹ * a₀ * v = a₀ := mul_inv_eq_one.mp hu1
  have hK' : Mem3 (conjSub v⁻¹ K) z := hK.conj_of_commute (inv_comm_of_comm hvz)
  have ha₀' : a₀ ∈ conjSub v⁻¹ K := by
    have := (hRinv a₀ ha₀).2
    rwa [hfix] at this
  have ha₀pg : IsPGroup 2 (Subgroup.zpowers a₀) := AscFusion.isPGroup_zpowers_of_sq_eq hz2 ha₀2
  have ha₀ord : orderOf a₀ = 4 :=
    AscFusion.orderOf_eq_four_of_sq_eq hz2 hK.isUniqueInvolution.ne_one ha₀2
  have hKK : K = conjSub v⁻¹ K :=
    hK.eq_of_mem_of_mem_same hK' ha₀.2 ha₀' ha₀pg (by omega)
  exact conjSub_inv_ne hv hKK.symm

end CFSG.ClassicalInvolution.Uniform.U4
