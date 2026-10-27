module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5FracEng
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5OneZ

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X] {n : ℕ} {z : X} {Z : Subgroup X}
  {S : Sylow 2 ↥(normalizer (Z : Set X))}

theorem le_oddCoreOf_of_cover {D G₁ R : Subgroup X} (hG₁D : G₁ ≤ D)
    (hcov : G₁ ⊔ pPrimeCoreOf 2 D = D) (hRG : R ≤ G₁) (hRn : G₁ ≤ normalizer (R : Set X))
    (hodd : Odd (Nat.card R)) : R ≤ oddCoreOf D := by
  classical
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcov' : G₁.subgroupOf D ⊔ pPrimeCore 2 ↥D = ⊤ := (covers_subgroupOf_iff hG₁D).2 hcov
  let ψ : ↥D →* ↥D ⧸ pPrimeCore 2 ↥D := QuotientGroup.mk' (pPrimeCore 2 ↥D)
  have hRD : R ≤ D := hRG.trans hG₁D
  set R₀ : Subgroup ↥D := R.subgroupOf D with hR₀
  have hψG : ∀ γ : ↥D ⧸ pPrimeCore 2 ↥D, ∃ g ∈ G₁.subgroupOf D, ψ g = γ := by
    intro γ
    obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective γ
    have hd : d ∈ G₁.subgroupOf D ⊔ pPrimeCore 2 ↥D := by rw [hcov']; exact Subgroup.mem_top d
    obtain ⟨e, he, o, ho, heo⟩ := Subgroup.mem_sup_of_normal_right.1 hd
    refine ⟨e, he, ?_⟩
    show QuotientGroup.mk e = QuotientGroup.mk d
    rw [← heo, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff o).2 ho, mul_one]
  have hPn : (R₀.map ψ).Normal := by
    refine ⟨fun p hp γ => ?_⟩
    obtain ⟨r, hr, rfl⟩ := hp
    obtain ⟨g, hg, rfl⟩ := hψG γ
    refine ⟨g * r * g⁻¹, ?_, by simp⟩
    show ((g * r * g⁻¹ : ↥D) : X) ∈ R
    have := (Subgroup.mem_normalizer_iff.1 (hRn hg) (r : X)).1 hr
    simpa using this
  have hPodd : Nat.Coprime 2 (Nat.card (R₀.map ψ)) := by
    have h1 : Nat.card (R₀.map ψ) ∣ Nat.card R₀ := Subgroup.card_map_dvd R₀ ψ
    have h2 : Nat.card R₀ = Nat.card R := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRD).toEquiv
    exact Nat.coprime_two_left.2 (Odd.of_dvd_nat (h2 ▸ hodd) h1)
  have hle : R₀.map ψ ≤ pPrimeCore 2 (↥D ⧸ pPrimeCore 2 ↥D) := le_sSup ⟨hPn, hPodd⟩
  rw [pPrimeCore_quotient_pPrimeCore_eq_bot 2] at hle
  intro r hr
  have h1 : ψ (⟨r, hRD hr⟩ : ↥D) ∈ R₀.map ψ := ⟨⟨r, hRD hr⟩, hr, rfl⟩
  have h2 := hle h1
  rw [Subgroup.mem_bot] at h2
  exact mem_oddCoreOf_iff.2 ⟨hRD hr, (QuotientGroup.eq_one_iff _).1 h2⟩

omit [Finite X] in
theorem exists_pow_three_eq_one_ne_one {K : Type} [Group K] (hn : 3 ≤ n)
    (C : AhatData.CoverSetup n K) : ∃ x : K, x ^ 3 = 1 ∧ x ≠ 1 := by
  classical
  let a : Fin n := ⟨0, by omega⟩
  let b : Fin n := ⟨1, by omega⟩
  let c : Fin n := ⟨2, by omega⟩
  have hab : a ≠ b := fun h => by simpa [a, b] using congrArg Fin.val h
  have hac : a ≠ c := fun h => by simpa [a, c] using congrArg Fin.val h
  have hbc : b ≠ c := fun h => by simpa [b, c] using congrArg Fin.val h
  have h3 : (swap a b * swap a c).IsThreeCycle :=
    Equiv.Perm.isThreeCycle_swap_mul_swap_same hab hac hbc
  obtain ⟨x₀, hx₀⟩ := C.exists_ρ_eq h3.sign
  have hord : orderOf (swap a b * swap a c) = 3 := h3.orderOf
  have hx3 : x₀ ^ 3 ∈ center K := by
    rw [← C.ρ_eq_one_iff, map_pow, hx₀, ← hord]
    exact pow_orderOf_eq_one _
  have hx6 : x₀ ^ 6 = 1 := by
    have := C.sq_of_mem_center hx3
    calc x₀ ^ 6 = x₀ ^ 3 * x₀ ^ 3 := by rw [← pow_add]
      _ = 1 := this
  refine ⟨x₀ ^ 4, ?_, ?_⟩
  · calc (x₀ ^ 4) ^ 3 = (x₀ ^ 6) ^ 2 := by rw [← pow_mul, ← pow_mul]
      _ = 1 := by rw [hx6, one_pow]
  · intro h1
    have h2 : C.ρ (x₀ ^ 4) = 1 := by rw [h1, map_one]
    rw [map_pow, hx₀] at h2
    have h4 : (swap a b * swap a c) ^ 4 = swap a b * swap a c := by
      have : (swap a b * swap a c) ^ 3 = 1 := by rw [← hord]; exact pow_orderOf_eq_one _
      calc (swap a b * swap a c) ^ 4 = (swap a b * swap a c) ^ 3 * (swap a b * swap a c) := by
            rw [← pow_succ]
        _ = swap a b * swap a c := by rw [this, one_mul]
    rw [h4] at h2
    have : orderOf (swap a b * swap a c) = 1 := orderOf_eq_one_iff.2 h2
    omega

theorem cover_join (h : Sec5Data X n z Z S) {u : X} (hu2' : orderOf u = 2)
    (huA : ∀ A : Subgroup X, Sec5Comp X n (normalizer (Z : Set X)) A →
      u ∈ centralizerSection A (pPrimeCoreOf 2 A)) :
    (K0 X n (normalizer (Z : Set X)) ⊓ LPlusIn (centralizer ({u} : Set X))) ⊔
      pPrimeCoreOf 2 (K0 X n (normalizer (Z : Set X))) = K0 X n (normalizer (Z : Set X)) := by
  set N : Subgroup X := normalizer (Z : Set X) with hN
  set D : Subgroup X := K0 X n N with hD
  have hDN : D ≤ N := K0_le n N
  have hND : N ≤ normalizer (D : Set X) := Sec5Data.le_normalizer_K0 X n N
  have hOD : oddCoreOf D = D ⊓ oddCoreOf N := oddCoreOf_eq_inf hDN hND
  refine le_antisymm (sup_le inf_le_left (oddCoreOf_le D)) ?_
  rw [hD, K0_eq_sSup_sec5Comp]
  refine sSup_le fun A hA => ?_
  have hAD : A ≤ D := le_sSup hA
  have hE₁A : A ⊓ LPlusIn (centralizer ({u} : Set X)) ≤ A := inf_le_left
  have hcov := (covers_subgroupOf_iff hE₁A).1 (exists_cover_LPlus h hA hu2' (huA A hA))
  have hOA : pPrimeCoreOf 2 A ≤ pPrimeCoreOf 2 D := by
    have h1 : oddCoreOf A ≤ oddCoreOf N := oddCoreOf_le_of_isPCompIn hA.isPCompIn
    have h2 : oddCoreOf A ≤ D := (oddCoreOf_le A).trans hAD
    show oddCoreOf A ≤ oddCoreOf D
    rw [hOD]
    exact le_inf h2 h1
  calc A = (A ⊓ LPlusIn (centralizer ({u} : Set X))) ⊔ pPrimeCoreOf 2 A := hcov.symm
    _ ≤ (D ⊓ LPlusIn (centralizer ({u} : Set X))) ⊔ pPrimeCoreOf 2 D :=
        sup_le_sup (inf_le_inf_right _ hAD) hOA

theorem false_of_swap (h : Sec5Data X n z Z S) {s : X} (hsN : s ∈ normalizer (Z : Set X)) {u : X}
    (hu2' : orderOf u = 2) (hus : u * s = s * u)
    (huA : ∀ A : Subgroup X, Sec5Comp X n (normalizer (Z : Set X)) A →
      u ∈ centralizerSection A (pPrimeCoreOf 2 A))
    {W : Subgroup X} (hW : IsPGroup 2 ↥W)
    (hWn : W ≤ normalizer (pPrimeCoreOf 2 (LPlusIn (centralizer ({u} : Set X))) : Set X))
    (hV : ∀ x ∈ LPlusIn (centralizer ({u} : Set X)),
      ⁅x, s⁆ ∈ pPrimeCoreOf 2 (LPlusIn (centralizer ({u} : Set X))) ⊔ W)
    {A : Subgroup X} (hA : Sec5Comp X n (normalizer (Z : Set X)) A)
    (hsA : s ∉ normalizer (A : Set X)) : False := by
  classical
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : 8 ≤ n := h.maxdeg.1
  set N : Subgroup X := normalizer (Z : Set X) with hN
  set D : Subgroup X := K0 X n N with hD
  have hDN : D ≤ N := K0_le n N
  have hND : N ≤ normalizer (D : Set X) := Sec5Data.le_normalizer_K0 X n N
  have hOD : oddCoreOf D = D ⊓ oddCoreOf N := oddCoreOf_eq_inf hDN hND
  set L : Subgroup X := LPlusIn (centralizer ({u} : Set X)) with hL
  set 𝒪 : Subgroup X := pPrimeCoreOf 2 L with h𝒪
  set G₁ : Subgroup X := D ⊓ L with hG₁
  have hcovG : G₁ ⊔ pPrimeCoreOf 2 D = D := cover_join h hu2' huA
  have hAD : A ≤ D := le_sSup hA
  have hAN : A ≤ N := hA.isPCompIn.1
  have hsD : s ∈ normalizer (D : Set X) := hND hsN
  have hsC : s ∈ centralizer ({u} : Set X) := Subgroup.mem_centralizer_singleton_iff.2 hus.symm
  set A'' : Subgroup X := A.map (MulAut.conj s).toMonoidHom with hA''
  have hA''c : Sec5Comp X n N A'' := hA.map_conj (Subgroup.le_normalizer hsN)
  have hne : A ≠ A'' := fun heq => hsA (mem_normalizer_of_map_conj_eq heq.symm)
  have hA''D : A'' ≤ D := le_sSup hA''c
  let C := AhatData.CoverSetup.ofCover hA.2
  obtain ⟨xb, hxb3, hxb1⟩ := exists_pow_three_eq_one_ne_one (by omega : 3 ≤ n) C
  have hcovA := exists_cover_LPlus h hA hu2' (huA A hA)
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective xb
  have ha : a ∈ (A ⊓ L).subgroupOf A ⊔ pPrimeCore 2 ↥A := by
    rw [hcovA]; exact Subgroup.mem_top a
  obtain ⟨e, he, o, ho, heo⟩ := Subgroup.mem_sup_of_normal_right.1 ha
  have hmk : (QuotientGroup.mk e : ↥A ⧸ pPrimeCore 2 ↥A) = QuotientGroup.mk a := by
    rw [← heo, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff o).2 ho, mul_one]
  rw [← hmk] at hxb3 hxb1
  set x : X := (e : X) with hx
  have hxA : x ∈ A := e.2
  have hxL : x ∈ L := (Subgroup.mem_inf.1 he).2
  have hx3A : x ^ 3 ∈ oddCoreOf A := by
    have h1 : e ^ 3 ∈ pPrimeCore 2 ↥A := (QuotientGroup.eq_one_iff _).1 (by
      rw [QuotientGroup.mk_pow]; exact hxb3)
    exact mem_oddCoreOf_iff.2 ⟨(e ^ 3).2, h1⟩
  have hxD : x ∈ D := hAD hxA
  have hx3D : x ^ 3 ∈ oddCoreOf D := by
    rw [hOD]
    exact ⟨D.pow_mem hxD 3, oddCoreOf_le_of_isPCompIn hA.isPCompIn hx3A⟩
  set y : X := s * x⁻¹ * s⁻¹ with hy
  have hyA'' : y ∈ A'' := ⟨x⁻¹, A.inv_mem hxA, by simp [hy, MulAut.conj_apply]⟩
  have hyL : y ∈ L :=
    (Subgroup.mem_normalizer_iff.1 (le_normalizer_LPlusIn _ hsC) x⁻¹).1 (L.inv_mem hxL)
  have hyD : y ∈ D := hA''D hyA''
  have hy3D : y ^ 3 ∈ oddCoreOf D := by
    have h1 : s * (x ^ 3)⁻¹ * s⁻¹ ∈ oddCoreOf D :=
      (Subgroup.mem_normalizer_iff.1 (mem_normalizer_oddCoreOf_of_mem_normalizer hsD) _).1
        ((oddCoreOf D).inv_mem hx3D)
    have h2 : y ^ 3 = s * (x ^ 3)⁻¹ * s⁻¹ := by simp only [hy, conj_pow, inv_pow]
    rw [h2]; exact h1
  set p : X := x * y with hp
  have hpcomm : ⁅x, s⁆ = p := by simp only [commutatorElement_def, hp, hy]; group
  have hpW : p ∈ 𝒪 ⊔ W := hpcomm ▸ hV x hxL
  obtain ⟨k, hk⟩ := exists_pow_two_mem_of_mem_sup hWn hW hpW
  have hpG : p ∈ G₁ := G₁.mul_mem ⟨hxD, hxL⟩ ⟨hyD, hyL⟩
  have hg𝒪 : ∀ g ∈ G₁, g ∈ normalizer (𝒪 : Set X) := fun g hg =>
    normalizer_le_normalizer_pPrimeCoreOf L (Subgroup.le_normalizer (Subgroup.mem_inf.1 hg).2)
  have hRn : G₁ ≤ normalizer ((G₁ ⊓ 𝒪 : Subgroup X) : Set X) := fun g hg =>
    mem_normalizer_inf (Subgroup.le_normalizer hg) (hg𝒪 g hg)
  have hRodd : Odd (Nat.card ↥(G₁ ⊓ 𝒪)) :=
    Odd.of_dvd_nat (odd_card_oddCoreOf L) (Subgroup.card_dvd_of_le inf_le_right)
  have hqD : p ^ (2 ^ k) ∈ oddCoreOf D :=
    le_oddCoreOf_of_cover inf_le_left hcovG inf_le_left hRn hRodd ⟨G₁.pow_mem hpG _, hk⟩
  let ψ : ↥D →* ↥D ⧸ pPrimeCore 2 ↥D := QuotientGroup.mk' (pPrimeCore 2 ↥D)
  have hψ1 : ∀ d : ↥D, (d : X) ∈ oddCoreOf D → ψ d = 1 := fun d hd =>
    (QuotientGroup.eq_one_iff _).2 (mem_oddCoreOf_iff.1 hd).2
  have hψ2 : ∀ d : ↥D, ψ d = 1 → (d : X) ∈ oddCoreOf D := fun d hd =>
    mem_oddCoreOf_iff.2 ⟨d.2, (QuotientGroup.eq_one_iff _).1 hd⟩
  let xD : ↥D := ⟨x, hxD⟩
  let yD : ↥D := ⟨y, hyD⟩
  have hcommD : ∀ (a' : X) (ha' : a' ∈ A), ψ ⟨a', hAD ha'⟩ * ψ yD = ψ yD * ψ ⟨a', hAD ha'⟩ := by
    intro a' ha'
    have h1 : ⁅a', y⁆ ∈ oddCoreOf N :=
      commutator_mem_oddCoreOf_of_ne hA.isPCompIn hA''c.isPCompIn hne ha' hyA''
    have h2 : ⁅a', y⁆ ∈ oddCoreOf D := by
      rw [hOD]
      refine ⟨?_, h1⟩
      simp only [commutatorElement_def]
      exact D.mul_mem (D.mul_mem (D.mul_mem (hAD ha') hyD) (D.inv_mem (hAD ha'))) (D.inv_mem hyD)
    have h3 : ψ ⁅(⟨a', hAD ha'⟩ : ↥D), yD⁆ = 1 := hψ1 _ h2
    rw [map_commutatorElement] at h3
    exact commutatorElement_eq_one_iff_mul_comm.1 h3
  have hxy : ψ xD * ψ yD = ψ yD * ψ xD := hcommD x hxA
  have hpD : ψ (xD * yD) = 1 := by
    have h3x : (ψ xD) ^ 3 = 1 := by
      rw [← map_pow]; exact hψ1 _ hx3D
    have h3y : (ψ yD) ^ 3 = 1 := by
      rw [← map_pow]; exact hψ1 _ hy3D
    have h3 : (ψ (xD * yD)) ^ 3 = 1 := by
      rw [map_mul, (Commute.mul_pow hxy 3), h3x, h3y, mul_one]
    have h2k : (ψ (xD * yD)) ^ (2 ^ k) = 1 := by
      rw [← map_pow]; exact hψ1 _ hqD
    have hdvd1 : orderOf (ψ (xD * yD)) ∣ 3 := orderOf_dvd_of_pow_eq_one h3
    have hdvd2 : orderOf (ψ (xD * yD)) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h2k
    have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
    have : orderOf (ψ (xD * yD)) = 1 := Nat.eq_one_of_dvd_coprimes hcop hdvd1 hdvd2
    exact orderOf_eq_one_iff.1 this
  have hxcent : ∀ a' ∈ A, ⁅a', x⁆ ∈ oddCoreOf A := by
    intro a' ha'
    have hxy1 : ψ xD = (ψ yD)⁻¹ := by
      rw [map_mul] at hpD; exact eq_inv_of_mul_eq_one_left hpD
    have hcomm' : ψ ⟨a', hAD ha'⟩ * ψ xD = ψ xD * ψ ⟨a', hAD ha'⟩ := by
      rw [hxy1]
      exact ((Commute.inv_right (show Commute (ψ ⟨a', hAD ha'⟩) (ψ yD) from hcommD a' ha'))).eq
    have h1 : ψ ⁅(⟨a', hAD ha'⟩ : ↥D), xD⁆ = 1 := by
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.2 hcomm'
    have h2 : ⁅a', x⁆ ∈ oddCoreOf D := hψ2 _ h1
    have h3 : ⁅a', x⁆ ∈ oddCoreOf N := by
      rw [hOD] at h2; exact h2.2
    have h4 : ⁅a', x⁆ ∈ A := by
      simp only [commutatorElement_def]
      exact A.mul_mem (A.mul_mem (A.mul_mem ha' hxA) (A.inv_mem ha')) (A.inv_mem hxA)
    exact inf_oddCoreOf_le hAN ⟨h4, h3⟩
  have hcen : (QuotientGroup.mk e : ↥A ⧸ pPrimeCore 2 ↥A) ∈
      Subgroup.center (↥A ⧸ pPrimeCore 2 ↥A) := by
    rw [Subgroup.mem_center_iff]
    intro k'
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective k'
    have h1 := hxcent (b : X) b.2
    have h2 : (QuotientGroup.mk' (pPrimeCore 2 ↥A)) ⁅b, e⁆ = 1 :=
      (QuotientGroup.eq_one_iff _).2 (mem_oddCoreOf_iff.1 h1).2
    rw [map_commutatorElement] at h2
    exact commutatorElement_eq_one_iff_mul_comm.1 h2
  have hsq := C.sq_of_mem_center hcen
  apply hxb1
  have h3' : (QuotientGroup.mk e : ↥A ⧸ pPrimeCore 2 ↥A) ^ 3 = QuotientGroup.mk e := by
    calc (QuotientGroup.mk e : ↥A ⧸ pPrimeCore 2 ↥A) ^ 3
        = QuotientGroup.mk e * QuotientGroup.mk e * QuotientGroup.mk e := by
          rw [pow_succ, pow_two]
      _ = QuotientGroup.mk e := by rw [hsq, one_mul]
  rw [← h3']
  exact hxb3

theorem Sec5Data.mem_centralizerSection_of_mem_Z (h : Sec5Data X n z Z S) {A : Subgroup X}
    (hA : Sec5Comp X n (normalizer (Z : Set X)) A) {u : X} (huZ : u ∈ Z) :
    u ∈ centralizerSection A (pPrimeCoreOf 2 A) := by
  have hAD : A ≤ K0 X n (normalizer (Z : Set X)) := le_sSup hA
  have hcomm : ∀ a ∈ A, a * u = u * a := fun a ha => (h.Z_le_center_K0 huZ (hAD ha)).symm
  have hN : u ∈ normalizer (A : Set X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have : u * y * u⁻¹ = y := by rw [← hcomm y hy]; group
      rw [this]; exact hy
    · intro hb
      have h1 := hcomm _ hb
      have h2 : u * y = u * (u * y * u⁻¹) := by
        calc u * y = (u * y * u⁻¹) * u := by group
          _ = u * (u * y * u⁻¹) := h1
      have h3 : y = u * y * u⁻¹ := mul_left_cancel h2
      rw [← h3] at hb
      exact hb
  have hc : CentModOdd A u := fun a ha => by
    rw [commutatorElement_eq_one_iff_mul_comm.2 (hcomm a ha)]
    exact one_mem _
  exact mem_QOf_iff.2 ⟨hN, hc⟩

theorem sec5_comm_of_K0_ne_bot (h : Sec5Data X n z Z S) {s : X} (hs : IsSec5Inv X Z s) {u : X}
    (huZ : u ∈ Z) (hu1 : u ≠ 1) (hus : u * s = s * u)
    (hcon : K0 X n (K0 X n (centralizer ({s} : Set X)) ⊓ centralizer ({u} : Set X)) ≠ ⊥) :
    ∀ k ∈ K0 X n (normalizer (Z : Set X)),
      ⁅k, s⁆ ∈ pPrimeCoreOf 2 (K0 X n (normalizer (Z : Set X))) := by
  classical
  set N : Subgroup X := normalizer (Z : Set X) with hN
  set D : Subgroup X := K0 X n N with hD
  have hDN : D ≤ N := K0_le n N
  have hND : N ≤ normalizer (D : Set X) := Sec5Data.le_normalizer_K0 X n N
  have hOD : oddCoreOf D = D ⊓ oddCoreOf N := oddCoreOf_eq_inf hDN hND
  have hu2' : orderOf u = 2 := h.orderOf_eq_two_of_mem_Z huZ hu1
  have hu2 : u * u = 1 := h.Z_sq_eq_one huZ
  have huA : ∀ A : Subgroup X, Sec5Comp X n N A → u ∈ centralizerSection A (pPrimeCoreOf 2 A) :=
    fun A hA => h.mem_centralizerSection_of_mem_Z hA huZ
  obtain ⟨W, hW, hWn, hV⟩ := exists_mirror_comm h hs hu2' hus hcon
  have hcomp : ∀ A : Subgroup X, Sec5Comp X n N A → CentModOdd A s := by
    intro A hA
    by_cases hsA : s ∈ normalizer (A : Set X)
    · exact sec5_centModOdd_of_K0_ne_bot h hs hA hsA hu1 hu2 hus (huA A hA) hcon
    · exact (false_of_swap h hs.mem hu2' hus huA hW hWn hV hA hsA).elim
  have hsD : s ∈ normalizer (D : Set X) := hND hs.mem
  have hsO : s ∈ normalizer (oddCoreOf D : Set X) := mem_normalizer_oddCoreOf_of_mem_normalizer hsD
  have hS' : ∀ A' ∈ {B : Subgroup X | Sec5Comp X n N B}, A' ≤ normalizer (oddCoreOf D : Set X) :=
    fun A' hA' => (le_sSup hA' : A' ≤ D).trans (le_normalizer_oddCoreOf D)
  have h' : ∀ A' ∈ {B : Subgroup X | Sec5Comp X n N B}, ∀ a' ∈ A', ⁅a', s⁆ ∈ oddCoreOf D := by
    intro A' hA' a' ha'
    have hA'D : A' ≤ D := le_sSup hA'
    have hmemD : ⁅a', s⁆ ∈ D := by
      have e : ⁅a', s⁆ = a' * (s * a'⁻¹ * s⁻¹) := by simp only [commutatorElement_def]; group
      rw [e]
      exact D.mul_mem (hA'D ha') ((Subgroup.mem_normalizer_iff.1 hsD _).1 (D.inv_mem (hA'D ha')))
    rw [hOD]
    exact ⟨hmemD, oddCoreOf_le_of_isPCompIn hA'.isPCompIn (hcomp A' hA' a' ha')⟩
  have := forall_comm_mem_of_sSup hsO hS' h'
  intro k hk
  exact this k (by rw [← K0_eq_sSup_sec5Comp]; exact hk)

theorem sec5_K0_inf_eq_bot (h : Sec5Data X n z Z S) {s : X} (hs : IsSec5Inv X Z s) {u : X}
    (huZ : u ∈ Z) (hu1 : u ≠ 1) (hus : u * s = s * u) :
    K0 X n (K0 X n (centralizer ({s} : Set X)) ⊓ centralizer ({u} : Set X)) = ⊥ := by
  by_contra hcon
  have hcomm := sec5_comm_of_K0_ne_bot h hs huZ hu1 hus hcon
  have hs1 : s ≠ 1 := fun h1 => hs.notMem (h1 ▸ one_mem Z)
  have hs2 : orderOf s = 2 := orderOf_eq_prime (by rw [sq]; exact hs.sq) hs1
  have hsyl := h.pair.isSylowTwoIn_zStar_K0_centralizer h.hypA h.maxdeg hs.mem hs2 hcomm
  obtain ⟨g, S₁, -, -, hS₁⟩ := h.exists_mirror_inv hs
  have hsz : s ∈ zStar (K0 X n (centralizer ({s} : Set X))) := hS₁.pair.sylow.1 hS₁.pair.mem
  exact hs.notMem (hsyl.mem_of_mem_normalizer hsz (isPGroup_zpowers_of_mul_self hs.sq) hs.mem)

end CFSG.OddStandard.Solomon75
