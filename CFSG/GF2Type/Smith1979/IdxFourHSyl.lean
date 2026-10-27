module

public import CFSG.GF2Type.Smith1979.IdxFourHLemma5
public import CFSG.GF2Type.Smith1979.IdxFourHFacts
public import CFSG.GF2Type.Smith1979.IdxFourHLin

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.IdxFour

open Subgroup Module QuadraticMap CFSG.LargeExtraspecial CFSG.RankThree.OrthogonalInvolutions
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem le_of_normal_isSylowTwoIn {P H N : Subgroup G} (hP : S5.IsSylowTwoIn P H) (hNH : N ≤ H)
    (hN2 : IsPGroup 2 N) (hnorm : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N) : N ≤ P := by
  obtain ⟨T, hT, hNT⟩ := S5.exists_isSylowTwoIn_ge hNH hN2
  obtain ⟨c, hcH, hc⟩ := hP.exists_conj hT
  intro n hn
  have hy : c * n * c⁻¹ ∈ N := hnorm c hcH n hn
  have := (hc _).mp (hNT hy)
  simpa [mul_assoc] using this

theorem isPGroup_zpowers_of_mul_self {x : G} (hxx : x * x = 1) : IsPGroup 2 (zpowers x) := by
  intro y
  refine ⟨1, ?_⟩
  apply Subtype.ext
  rcases (Setting.mem_zpowers_iff_of_mul_self hxx).mp y.2 with h | h
  · simp [h]
  · simp [h, pow_two, hxx]

theorem mem_of_isSylowTwoIn_centralizer {P H : Subgroup G} {x : G} (hP : S5.IsSylowTwoIn P H)
    (hxH : x ∈ H) (hxx : x * x = 1) (hcomm : ∀ h ∈ H, h * x = x * h) : x ∈ P := by
  have : zpowers x ≤ P := by
    refine le_of_normal_isSylowTwoIn hP (zpowers_le.mpr hxH) (isPGroup_zpowers_of_mul_self hxx)
      ?_
    intro h hh n hn
    rcases (Setting.mem_zpowers_iff_of_mul_self hxx).mp hn with rfl | rfl
    · simpa using one_mem _
    · have := hcomm h hh
      rw [this, mul_assoc, mul_inv_cancel, mul_one]
      exact mem_zpowers _
  exact this (mem_zpowers _)

variable (S) in
theorem exists_sylow_centralizer (hTI : WeaklyClosedTITransitive.{0}) (hw : S.width = 6)
    (hirr : ¬ S.IsReducible) (hnoAll : S11.NoA2All S) {g : G} {K : Subgroup S.O}
    {θ xb : S.O} (hF : IdxFourFacts S g K θ xb) {x : G} (hxM : x ∈ S.M) (hxx : x * x = 1)
    (hρx : S.ρ ⟨x, hxM⟩ = xb) {U : Submodule (ZMod 2) S.Qt} (hU9 : 9 ≤ finrank (ZMod 2) U)
    (hUF : U ≤ fixO S xb) (hUc : ∀ y ∈ S.clPre U, y * x = x * y)
    (hUW : ∀ y : S.Qt, (∀ v ∈ U, polar S.q y v = 0) → S.q y = 0 → y ∈ commO S xb) :
    ∃ T : Subgroup G, S5.IsSylowTwoIn T (centralizer ({x} : Set G)) ∧ Nat.card T ≤ 2 ^ 19 := by
  classical
  have hq12 : finrank (ZMod 2) S.Qt = 12 := by rw [S.finrank_Qt_eq_two_mul_width, hw]
  have hFdim : finrank (ZMod 2) (fixO S xb) = 10 := by
    have := finrank_commO_add_fixO xb
    rw [hF.x_dim, hq12] at this
    omega
  set C : Subgroup G := centralizer ({x} : Set G) ⊓ centralizer ({S.z} : Set G) with hC
  obtain ⟨T, hT, -⟩ := S5.exists_isSylowTwoIn_ge (bot_le : (⊥ : Subgroup G) ≤ C) IsPGroup.of_bot
  have hTC : T ≤ C := hT.le
  have hTx : T ≤ centralizer ({x} : Set G) := hTC.trans inf_le_left
  have hTM : T ≤ S.M := hTC.trans inf_le_right
  have hNT : S.QG ⊓ centralizer ({x} : Set G) ≤ T := by
    refine le_of_normal_isSylowTwoIn hT ?_ (S.isPGroup_QG.to_le inf_le_left) ?_
    · exact fun y hy => ⟨hy.2, S.QG_le_M hy.1⟩
    · intro h hh n hn
      refine ⟨S.conj_mem_QG hh.2 hn.1, ?_⟩
      have h1 := mem_centralizer_singleton_iff.mp hh.1
      have h2 := mem_centralizer_singleton_iff.mp hn.2
      show h * n * h⁻¹ ∈ centralizer ({x} : Set G)
      rw [mem_centralizer_singleton_iff]
      calc h * n * h⁻¹ * x = h * n * (h⁻¹ * x) := by group
        _ = h * n * (x * h⁻¹) := by
            congr 1
            calc h⁻¹ * x = h⁻¹ * (x * h) * h⁻¹ := by group
              _ = h⁻¹ * (h * x) * h⁻¹ := by rw [h1]
              _ = x * h⁻¹ := by group
        _ = h * (n * x) * h⁻¹ := by group
        _ = h * (x * n) * h⁻¹ := by rw [h2]
        _ = x * (h * n * h⁻¹) := by
            calc h * (x * n) * h⁻¹ = (h * x) * n * h⁻¹ := by group
              _ = (x * h) * n * h⁻¹ := by rw [h1]
              _ = x * (h * n * h⁻¹) := by group
  have hxT : x ∈ T :=
    mem_of_isSylowTwoIn_centralizer hT ⟨mem_centralizer_singleton_iff.mpr rfl,
      mem_centralizer_singleton_iff.mpr (S.mem_M_iff.mp hxM)⟩ hxx
      (fun h hh => mem_centralizer_singleton_iff.mp hh.1)
  have hzT : S.z ∈ T :=
    mem_of_isSylowTwoIn_centralizer hT ⟨mem_centralizer_singleton_iff.mpr (S.mem_M_iff.mp hxM).symm,
      mem_centralizer_singleton_iff.mpr rfl⟩ S.z_mul_z
      (fun h hh => mem_centralizer_singleton_iff.mp hh.2)
  have hQT : ∀ y ∈ S.clPre U, y ∈ T := fun y hy =>
    hNT ⟨hy.1, mem_centralizer_singleton_iff.mpr (hUc y hy)⟩
  have hUcl : ∀ v ∈ U, ∃ w ∈ S.clPre U, w ∈ S.QG ∧ S.cl w = v := by
    intro v hv
    have hv' : v ∈ S.clSub (S.clPre U) := by rw [S.clSub_clPre]; exact hv
    exact S.mem_clSub_iff.mp hv'
  have hzTT : S.z ∈ ⁅T, T⁆ := by
    obtain ⟨u₁, hu₁, u₂, hu₂, hne⟩ := exists_polar_ne_zero hq12 (U := U) (by omega)
    obtain ⟨w₁, hw₁, hw₁Q, rfl⟩ := hUcl u₁ hu₁
    obtain ⟨w₂, hw₂, hw₂Q, rfl⟩ := hUcl u₂ hu₂
    have hnc : w₁ * w₂ ≠ w₂ * w₁ := fun h => hne ((S.polar_cl_eq_zero_iff hw₁Q hw₂Q).mpr h)
    have hc := commutator_mem_commutator (hQT w₁ hw₁) (hQT w₂ hw₂)
    rcases S.commutator_eq_one_or_z hw₁Q hw₂Q with h | h
    · exfalso
      apply hnc
      calc w₁ * w₂ = w₁ * w₂ * w₁⁻¹ * w₂⁻¹ * (w₂ * w₁) := by group
        _ = w₂ * w₁ := by rw [h, one_mul]
    · rwa [commutatorElement_def, h] at hc
  have hzcent : S.z ∈ centralizer (T : Set G) :=
    mem_centralizer_iff.mpr fun t ht => S.z_comm (hTM ht)
  have huniq : ∀ h : G, h * S.z * h⁻¹ ∈ centralizer (T : Set G) → h * S.z * h⁻¹ ∈ ⁅T, T⁆ →
      h * S.z * h⁻¹ = S.z := by
    intro h hcent hcomm
    set k : G := h * S.z * h⁻¹ with hk
    have hkM : k ∈ S.M := S.mem_M_iff.mpr (mem_centralizer_iff.mp hcent S.z hzT).symm
    have hkK : k ∈ pre S K := comm_le_pre hF.K_le hF.K_index (commutator_mono hTM hTM hcomm)
    have hkk : k * k = 1 := by
      calc k * k = h * (S.z * S.z) * h⁻¹ := by rw [hk]; group
        _ = 1 := by rw [S.z_mul_z]; group
    set kb : S.O := S.ρ ⟨k, hkM⟩ with hkb
    have hkbK : kb ∈ K := rho_mem_of_mem_pre hkK hkM
    have hkb2 : kb * kb = 1 := by
      have : (⟨k, hkM⟩ : S.M) * ⟨k, hkM⟩ = 1 := Subtype.ext hkk
      rw [hkb, ← map_mul, this, map_one]
    have hUfix : U ≤ fixO S kb := by
      intro v hv
      obtain ⟨w, hw, hwQ, rfl⟩ := hUcl v hv
      have hkw : w * k = k * w := mem_centralizer_iff.mp hcent w (hQT w hw)
      rw [mem_fixO, hkb, S.ρ_cl ⟨k, hkM⟩ hwQ]
      congr 1
      calc k * w * k⁻¹ = (k * w) * k⁻¹ := rfl
        _ = (w * k) * k⁻¹ := by rw [hkw]
        _ = w := by group
    have hkb1 : kb = 1 := by
      by_contra hne1
      have h8 := hF.finrank_fixO_le hq12 hkbK hne1 hkb2
      have := Submodule.finrank_mono hUfix
      omega
    have hkQ : k ∈ S.QG := (S.ρ_eq_one_iff ⟨k, hkM⟩).mp hkb1
    have hperp : ∀ v ∈ U, polar S.q (S.cl k) v = 0 := by
      intro v hv
      obtain ⟨w, hw, hwQ, rfl⟩ := hUcl v hv
      have hkw : w * k = k * w := mem_centralizer_iff.mp hcent w (hQT w hw)
      exact (S.polar_cl_eq_zero_iff hkQ hwQ).mpr hkw.symm
    have hkq : S.q (S.cl k) = 0 := (S.q_cl_eq_zero_iff hkQ).mpr (by rw [pow_two]; exact hkk)
    have hW : S.cl k ∈ commO S xb := hUW _ hperp hkq
    by_cases hcl0 : S.cl k = 0
    · rcases (S.cl_eq_zero_iff hkQ).mp hcl0 with h1 | h1
      · exact absurd h1 (S4.conj_z_ne_one S h)
      · exact h1
    · exfalso
      have hne : k ≠ S.z := fun h' => hcl0 (by rw [h']; exact S.cl_z)
      exact no_conj_z_class_mem hTI hw hirr hnoAll (W := commO S xb) hF.lemma5 hkQ hne hW
  have hS : S5.IsSylowTwoIn T (centralizer ({x} : Set G)) :=
    isSylowTwoIn_centralizer_of_unique hT huniq hzcent hzTT
  refine ⟨T, hS, ?_⟩
  set f : T →* S.O := S.ρ.comp (inclusion hTM) with hf
  have hmul := card_ker_mul_card_range f
  have hxcl : ∀ t : T, (t : G) * x = x * t := fun t => mem_centralizer_singleton_iff.mp (hTx t.2)
  have hrange_le : f.range ≤ S.Mbar ⊓ centralizer ({xb} : Set S.O) := by
    rintro _ ⟨t, rfl⟩
    refine ⟨⟨_, rfl⟩, ?_⟩
    show f t ∈ centralizer ({xb} : Set S.O)
    rw [mem_centralizer_singleton_iff, ← hρx]
    change S.ρ ⟨t, hTM t.2⟩ * S.ρ ⟨x, hxM⟩ = S.ρ ⟨x, hxM⟩ * S.ρ ⟨t, hTM t.2⟩
    rw [← map_mul, ← map_mul]
    exact congrArg S.ρ (Subtype.ext (hxcl t))
  have hrange : Nat.card f.range ≤ 2 ^ 8 := by
    obtain ⟨j, hj⟩ := hT.isPGroup.exists_card_eq
    have hdvd : Nat.card f.range ∣ 2 ^ j := hj ▸ card_range_dvd f
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    by_contra hbig
    push Not at hbig
    have h9 : 9 ≤ i := by
      by_contra hlt
      push Not at hlt
      have : 2 ^ i ≤ 2 ^ 8 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    apply hF.x_cent
    calc 2 ^ 9 ∣ 2 ^ i := pow_dvd_pow 2 h9
      _ = Nat.card f.range := hi.symm
      _ ∣ _ := Subgroup.card_dvd_of_le hrange_le
  have hker : Nat.card f.ker ≤ 2 ^ 11 := by
    have hker' : ∀ t : f.ker, ((t : T) : G) ∈ S.clPre (fixO S xb) := by
      intro t
      have hρ1 : S.ρ ⟨((t : T) : G), hTM (t : T).2⟩ = 1 := t.2
      have htQ : ((t : T) : G) ∈ S.QG := (S.ρ_eq_one_iff _).mp hρ1
      refine ⟨htQ, ?_⟩
      rw [mem_fixO, ← hρx, S.ρ_cl ⟨x, hxM⟩ htQ]
      congr 1
      have := hxcl (t : T)
      calc x * ((t : T) : G) * x⁻¹ = (x * (t : G)) * x⁻¹ := rfl
        _ = ((t : G) * x) * x⁻¹ := by rw [this]
        _ = (t : G) := by group
    have hinj : Function.Injective
        (fun t : f.ker => (⟨((t : T) : G), hker' t⟩ : S.clPre (fixO S xb))) := by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun y : S.clPre (fixO S xb) => (y : G)) hab
    have h1 := Nat.card_le_card_of_injective _ hinj
    rw [S.card_clPre, S.card_submodule, hFdim] at h1
    simpa [pow_succ, mul_comm] using h1
  rw [← hmul]
  calc Nat.card f.ker * Nat.card f.range ≤ 2 ^ 11 * 2 ^ 8 := Nat.mul_le_mul hker hrange
    _ = 2 ^ 19 := by norm_num

end CFSG.GF2Type.Smith1979.IdxFour
