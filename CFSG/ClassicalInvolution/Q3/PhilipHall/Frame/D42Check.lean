module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.D42Exit
public import CFSG.ClassicalInvolution.Q3.Q3TLTO8
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeMain
public import Certificates.Certificate118001

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.D42

open CFSG.EvenSmallLie.OmegaEight CFSG.Certificates CFSG.Certificates.Native
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native
  CFSG.Sporadic.SmallOddCore CFSG.ComponentClassification.J2Cover
  CFSG.ClassicalInvolution.Q3.O8 CFSG.ClassicalInvolution.O8Data
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.D42Data

section Sylow

theorem exists_conj_mem_of_index {G : Type*} [Group G] [Finite G] {C P : Subgroup G}
    (hPC : P ≤ C) {e : ℕ} (hPcard : Nat.card P = 3 ^ e)
    (hidx : ¬ 3 ∣ Nat.card C / Nat.card P) {x : G} (hx : x ∈ C)
    (hx3 : ∃ k : ℕ, x ^ 3 ^ k = 1) : ∃ c ∈ C, c * x * c⁻¹ ∈ P := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set P' : Subgroup C := P.subgroupOf C with hP'
  have hP'card : Nat.card P' = Nat.card P :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPC).toEquiv
  have hP'p : IsPGroup 3 P' := IsPGroup.of_card (by rw [hP'card, hPcard])
  have hindex : P'.index = Nat.card C / Nat.card P := by
    have h := P'.card_mul_index
    rw [hP'card] at h
    have hpos : 0 < Nat.card P := Nat.card_pos
    rw [← h, Nat.mul_div_cancel_left _ hpos]
  have hnd : ¬ 3 ∣ P'.index := hindex ▸ hidx
  let x' : C := ⟨x, hx⟩
  have hX : IsPGroup 3 (Subgroup.zpowers x') := by
    obtain ⟨k, hk⟩ := hx3
    have hk' : x' ^ 3 ^ k = 1 := Subtype.ext (by simpa [x'] using hk)
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hk')
    exact IsPGroup.of_card (by rw [Nat.card_zpowers, hj])
  obtain ⟨Q, hQ⟩ := hX.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq C (hP'p.toSylow hnd) Q
  have h1 : x' ∈ (Q : Subgroup C) := hQ (Subgroup.mem_zpowers x')
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    MulAut.smul_def, MulAut.inv_def, MulAut.conj_symm_apply, IsPGroup.toSylow_coe, hP',
    Subgroup.mem_subgroupOf] at h1
  refine ⟨((g⁻¹ : C) : G), (g⁻¹ : C).2, ?_⟩
  simpa [x'] using h1

end Sylow

section Class

theorem ncard_conjClass_omegaT_le (b : Equiv.Perm (Fin 360)) :
    (CFSG.Sporadic.Schreier.conjClass omegaT b).ncard ≤ (CFSG.Sporadic.Schreier.conjClass autT b).ncard :=
  Set.ncard_le_ncard (fun _ ⟨c, hc, hx⟩ => ⟨c, omegaT_le_autT hc, hx⟩) (CFSG.Sporadic.Schreier.conjClass_finite autT b)

theorem card_centralizerIn_mul_le {b : Equiv.Perm (Fin 360)} {m : ℕ}
    (hm : m ≤ (CFSG.Sporadic.Schreier.conjClass autT b).ncard) : Nat.card (centralizerIn autT b) * m ≤ 1045094400 := by
  have hos := CFSG.Sporadic.Schreier.ncard_conjClass_mul_card autT b
  rw [card_autT] at hos
  calc Nat.card (centralizerIn autT b) * m
      ≤ Nat.card (centralizerIn autT b) * (CFSG.Sporadic.Schreier.conjClass autT b).ncard := Nat.mul_le_mul_left _ hm
    _ = 1045094400 := by rw [mul_comm]; exact hos

theorem exists_cent_le {i c : ℕ} (hc : Nat.card (centralizerIn omegaT (mainPerm i)) = c) :
    ∃ K : Subgroup (Equiv.Perm (Fin 360)), K ≤ centralizerIn autT (mainPerm i) ∧ K ≤ omegaT ∧
      Nat.card K = c :=
  ⟨centralizerIn omegaT (mainPerm i), fun _ hx => mem_centralizerIn.2
    ⟨omegaT_le_autT (mem_centralizerIn.1 hx).1, (mem_centralizerIn.1 hx).2⟩,
    fun _ hx => (mem_centralizerIn.1 hx).1, hc⟩

theorem class_le_of_card {i c m : ℕ} (hc : Nat.card (centralizerIn omegaT (mainPerm i)) = c)
    (hm : m * c = 174182400) :
    m ≤ (CFSG.Sporadic.Schreier.conjClass autT (mainPerm i)).ncard := by
  have h := CFSG.Sporadic.Schreier.ncard_conjClass_mul_card omegaT (mainPerm i)
  have hpos : 0 < c := hc ▸ Nat.card_pos
  rw [hc, card_omegaT, ← hm] at h
  rw [← Nat.eq_of_mul_eq_mul_right hpos h]
  exact ncard_conjClass_omegaT_le _

end Class

section Outer

theorem classC2_le : 11340 ≤ (CFSG.Sporadic.Schreier.conjClass autT (mainPerm 1)).ncard := by
  have h3 := CFSG.Sporadic.Schreier.ncard_conjClass_mul_card omegaT (mainPerm 1)
  rw [Certificates.certificate272020.2.2.1, card_omegaT] at h3
  have h := Certificates.certificate118001.1
  omega

theorem mem_omegaT_of_c2 {x : Equiv.Perm (Fin 360)} (hx : x ∈ centralizerIn autT (mainPerm 1))
    (hx3 : ∃ k : ℕ, x ^ 3 ^ k = 1) : x ∈ omegaT := by
  obtain ⟨K, hKC, hKO, hKcard⟩ := exists_cent_le Certificates.certificate272020.2.2.1
  have hbound := card_centralizerIn_mul_le classC2_le
  set C := centralizerIn autT (mainPerm 1) with hCdef
  set K' : Subgroup C := K.subgroupOf C with hK'
  have hK'card : Nat.card K' = 46080 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKC).toEquiv, hKcard]
  have hidx : K'.index = 1 ∨ K'.index = 2 := by
    have h := K'.card_mul_index
    rw [hK'card] at h
    have hne : K'.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have hle : 46080 * K'.index * 11340 ≤ 1045094400 := by rw [h]; exact hbound
    omega
  let x' : C := ⟨x, hx⟩
  have hx'K : x' ∈ K' := by
    rcases hidx with h | h
    · rw [Subgroup.index_eq_one.mp h]
      exact Subgroup.mem_top _
    · have hsq := Subgroup.sq_mem_of_index_two h x'
      obtain ⟨k, hk⟩ := hx3
      have hk' : x' ^ 3 ^ k = 1 := Subtype.ext (by simpa [x'] using hk)
      obtain ⟨m, hm⟩ : Odd (3 ^ k) := Odd.pow (by decide)
      have h2 : x' * (x' ^ 2) ^ m = 1 := by
        rw [← pow_mul, ← pow_succ', show 2 * m + 1 = 3 ^ k by omega, hk']
      rw [eq_inv_of_mul_eq_one_left h2]
      exact K'.inv_mem (K'.pow_mem hsq m)
  exact hKO ((Subgroup.mem_subgroupOf).1 hx'K)

theorem exists_conj_mem_sylow {j : ℕ} (hj : j < 2) {P : Subgroup (Equiv.Perm (Fin 360))}
    (hPC : P ≤ centralizerIn autT (mainPerm (mainIdx j))) (hPcard : Nat.card P = pOrder j)
    {x : Equiv.Perm (Fin 360)}
    (hx : x ∈ centralizerIn autT (mainPerm (mainIdx j))) (hx3 : ∃ k : ℕ, x ^ 3 ^ k = 1) :
    ∃ c ∈ centralizerIn autT (mainPerm (mainIdx j)), c * x * c⁻¹ ∈ P := by
  obtain ⟨-, hc0, -, hc2⟩ := Certificates.certificate272020
  interval_cases j
  · have hmi : mainIdx 0 = 0 := rfl
    rw [hmi] at hx hPC ⊢
    obtain ⟨K, hKC, -, hKcard⟩ := exists_cent_le hc0
    have hbound := card_centralizerIn_mul_le (class_le_of_card (m := 1575) hc0 (by norm_num))
    refine exists_conj_mem_of_index hPC (e := 4) (by rw [hPcard]; rfl) ?_ hx hx3
    have hKd : Nat.card K ∣ Nat.card (centralizerIn autT (mainPerm 0)) :=
      Subgroup.card_dvd_of_le hKC
    have hPd : Nat.card P ∣ Nat.card (centralizerIn autT (mainPerm 0)) :=
      Subgroup.card_dvd_of_le hPC
    have hpos : 0 < Nat.card (centralizerIn autT (mainPerm 0)) := Nat.card_pos
    rw [hKcard] at hKd
    rw [hPcard] at hPd ⊢
    norm_num [pOrder] at hKd hPd ⊢
    obtain ⟨t, ht⟩ := hKd
    rw [ht] at hbound hPd hpos ⊢
    have ht6 : t ≤ 6 := by omega
    interval_cases t <;> omega
  · have hmi : mainIdx 1 = 2 := rfl
    rw [hmi] at hx hPC ⊢
    obtain ⟨K, hKC, -, hKcard⟩ := exists_cent_le hc2
    have hbound := card_centralizerIn_mul_le (class_le_of_card (m := 56700) hc2 (by norm_num))
    refine exists_conj_mem_of_index hPC (e := 2) (by rw [hPcard]; rfl) ?_ hx hx3
    have hKd : Nat.card K ∣ Nat.card (centralizerIn autT (mainPerm 2)) :=
      Subgroup.card_dvd_of_le hKC
    have hPd : Nat.card P ∣ Nat.card (centralizerIn autT (mainPerm 2)) :=
      Subgroup.card_dvd_of_le hPC
    have hpos : 0 < Nat.card (centralizerIn autT (mainPerm 2)) := Nat.card_pos
    rw [hKcard] at hKd
    rw [hPcard] at hPd ⊢
    norm_num [pOrder] at hKd hPd ⊢
    obtain ⟨t, ht⟩ := hKd
    rw [ht] at hbound hPd hpos ⊢
    have ht6 : t ≤ 6 := by omega
    interval_cases t <;> omega

end Outer

section Model

theorem outer_criterion {z x : Equiv.Perm (Fin 360)} (hz : z ∈ omegaT) (hz2 : orderOf z = 2)
    (hx : x ∈ autT) (hxO : x ∉ omegaT) (hx3 : ∃ k : ℕ, x ^ 3 ^ k = 1) (hxz : x * z = z * x) :
    ∃ U : Subgroup (Equiv.Perm (Fin 360)), IsPGroup 2 U ∧ U ≤ omegaT ∧
      U ≤ Subgroup.centralizer ({z} : Set _) ∧
      x ∈ Subgroup.normalizer (U : Set (Equiv.Perm (Fin 360))) ∧
      9 ≤ Nat.card ↥⁅U, Subgroup.zpowers x⁆ := by
  obtain ⟨i, hi, g, hg, hzg⟩ := CFSG.ClassicalInvolution.Q3.O8.exists_conj_main hz hz2
  set x₁ := g⁻¹ * x * g with hx₁
  have hgi : g⁻¹ ∈ autT := autT.inv_mem hg
  have hx₁A : x₁ ∈ autT := autT.mul_mem (autT.mul_mem hgi hx) hg
  have hx₁c : x₁ * mainPerm i = mainPerm i * x₁ := by
    have e : mainPerm i = g⁻¹ * z * g := by rw [hzg]; group
    rw [e, hx₁]
    calc g⁻¹ * x * g * (g⁻¹ * z * g) = g⁻¹ * (x * z) * g := by group
      _ = g⁻¹ * (z * x) * g := by rw [hxz]
      _ = g⁻¹ * z * g * (g⁻¹ * x * g) := by group
  have hx₁C : x₁ ∈ centralizerIn autT (mainPerm i) := mem_centralizerIn.2 ⟨hx₁A, hx₁c⟩
  have hx₁O : x₁ ∉ omegaT := by
    intro h
    apply hxO
    have := (conj_mem_omegaT hg).1 h
    rwa [show g * x₁ * g⁻¹ = x by rw [hx₁]; group] at this
  have hx₁3 : ∃ k : ℕ, x₁ ^ 3 ^ k = 1 := by
    obtain ⟨k, hk⟩ := hx3
    refine ⟨k, ?_⟩
    have hc := conj_pow (a := g⁻¹) (b := x) (i := 3 ^ k)
    rw [inv_inv] at hc
    rw [hx₁, hc, hk]
    group
  obtain ⟨j, hj, hji⟩ : ∃ j < 2, mainIdx j = i := by
    interval_cases i
    · exact ⟨0, by norm_num, rfl⟩
    · exact absurd (mem_omegaT_of_c2 hx₁C hx₁3) hx₁O
    · exact ⟨1, by norm_num, rfl⟩
  subst hji
  obtain ⟨P, U, hPC, hPcard, hU2, hUO, hUC, hPN, h9P⟩ := Certificates.certificate118001.2 j hj
  obtain ⟨c, hcC, hcP⟩ := exists_conj_mem_sylow hj hPC hPcard hx₁C hx₁3
  obtain ⟨hcA, hcz⟩ := mem_centralizerIn.1 hcC
  have hyO : c * x₁ * c⁻¹ ∉ omegaT := fun h => hx₁O ((conj_mem_omegaT hcA).2 h)
  have hyN := hPN hcP
  have h9 := h9P _ hcP fun h => hyO (by rw [h]; exact omegaT.one_mem)
  set h := g * c⁻¹ with hhdef
  have hhA : h ∈ autT := autT.mul_mem hg (autT.inv_mem hcA)
  have hxh : x = h * (c * x₁ * c⁻¹) * h⁻¹ := by rw [hhdef, hx₁]; group
  have hzh : z = h * mainPerm (mainIdx j) * h⁻¹ := by
    have e : c⁻¹ * mainPerm (mainIdx j) * c = mainPerm (mainIdx j) := by
      calc c⁻¹ * mainPerm (mainIdx j) * c = c⁻¹ * (mainPerm (mainIdx j) * c) := by group
        _ = c⁻¹ * (c * mainPerm (mainIdx j)) := by rw [hcz]
        _ = mainPerm (mainIdx j) := by group
    rw [hzg, hhdef]
    calc g * mainPerm (mainIdx j) * g⁻¹ = g * (c⁻¹ * mainPerm (mainIdx j) * c) * g⁻¹ := by rw [e]
      _ = g * c⁻¹ * mainPerm (mainIdx j) * (g * c⁻¹)⁻¹ := by group
  set f : Equiv.Perm (Fin 360) ≃* Equiv.Perm (Fin 360) := MulAut.conj h with hf
  refine ⟨U.map f.toMonoidHom, hU2.map _, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨u, hu, rfl⟩
    exact (conj_mem_omegaT hhA).1 (hUO hu)
  · rintro _ ⟨u, hu, rfl⟩
    have hu' := Subgroup.mem_centralizer_singleton_iff.1 (hUC hu)
    rw [Subgroup.mem_centralizer_singleton_iff, hzh]
    show h * u * h⁻¹ * (h * mainPerm (mainIdx j) * h⁻¹) = h * mainPerm (mainIdx j) * h⁻¹ * (h * u * h⁻¹)
    calc h * u * h⁻¹ * (h * mainPerm (mainIdx j) * h⁻¹) = h * (u * mainPerm (mainIdx j)) * h⁻¹ := by
          group
      _ = h * (mainPerm (mainIdx j) * u) * h⁻¹ := by rw [hu']
      _ = h * mainPerm (mainIdx j) * h⁻¹ * (h * u * h⁻¹) := by group
  · rw [← Subgroup.map_equiv_normalizer_eq U f]
    exact ⟨c * x₁ * c⁻¹, hyN, hxh.symm⟩
  · have hzp : Subgroup.zpowers x = (Subgroup.zpowers (c * x₁ * c⁻¹)).map f.toMonoidHom := by
      rw [MonoidHom.map_zpowers]
      exact congrArg Subgroup.zpowers hxh
    rw [hzp, ← Subgroup.map_commutator, Subgroup.card_map_of_injective f.injective]
    exact h9

end Model

section Exit

theorem d42OuterCommutator_proved : D42OuterCommutator := by
  intro Y _ _ T hTn hC _ hLie z hzT hz2 x hxT hx3 hxz
  have hBl : CFSG.Blueprint.LieModel ↥T .POmegaPlus 4 2 1 := by
    rcases hLie.2 with hc | ⟨h0, -⟩
    · exact Or.inl ⟨by decide, hc⟩
    · exact absurd h0 (by norm_num)
  obtain ⟨e⟩ := nonempty_mulEquiv_omegaT hBl
  let φ : Y →* ↥autT :=
    autEquiv.symm.toMonoidHom.comp ((MulAut.congr e).toMonoidHom.comp MulAut.conjNormal)
  let Φ : Y →* Equiv.Perm (Fin 360) := autT.subtype.comp φ
  have hΦT : ∀ (t : Y) (ht : t ∈ T), Φ t = ((e ⟨t, ht⟩ : omegaT) : Equiv.Perm (Fin 360)) := by
    intro t ht
    have h1 : (MulAut.conjNormal t : MulAut ↥T) = MulAut.conj (⟨t, ht⟩ : ↥T) :=
      MulAut.conjNormal_val (h := (⟨t, ht⟩ : ↥T))
    have h2 : MulAut.congr e (MulAut.conj (⟨t, ht⟩ : ↥T)) = MulAut.conj (e ⟨t, ht⟩) :=
      CFSG.ComponentClassification.OuterAutomorphisms.congr_conj e _
    have h3 : autEquiv.symm (MulAut.conj (e ⟨t, ht⟩)) =
        ⟨((e ⟨t, ht⟩ : omegaT) : Equiv.Perm (Fin 360)), omegaT_le_autT (e ⟨t, ht⟩).2⟩ := by
      rw [MulEquiv.symm_apply_eq, autEquiv_omegaT]
    show ((autEquiv.symm (MulAut.congr e (MulAut.conjNormal t)) : ↥autT) :
      Equiv.Perm (Fin 360)) = _
    rw [h1, h2, h3]
  have hΦinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    intro y hy
    have hφ : φ y = 1 := Subtype.ext hy
    have hc : MulAut.congr e (MulAut.conjNormal y) = 1 := by
      have := congrArg autEquiv hφ
      simpa [φ] using this
    have hcn : (MulAut.conjNormal y : MulAut ↥T) = 1 :=
      (MulAut.congr e).injective (hc.trans (map_one _).symm)
    have hyC : y ∈ Subgroup.centralizer (T : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      have := congrArg (fun φ' : MulAut ↥T => ((φ' ⟨t, ht⟩ : ↥T) : Y)) hcn
      simp only [MulAut.conjNormal_apply, MulAut.one_apply] at this
      calc t * y = y * t * y⁻¹ * y := by rw [this]
        _ = y * t := by group
    rw [hC, Subgroup.mem_bot] at hyC
    exact hyC
  have hrange : ∀ w ∈ omegaT, ∃ s : ↥T, Φ s = w := by
    intro w hw
    refine ⟨e.symm ⟨w, hw⟩, ?_⟩
    rw [hΦT _ (e.symm ⟨w, hw⟩).2]
    simp
  have hzO : Φ z ∈ omegaT := by rw [hΦT z hzT]; exact (e ⟨z, hzT⟩).2
  have hzo : orderOf (Φ z) = 2 := by rw [orderOf_injective Φ hΦinj, hz2]
  have hxA : Φ x ∈ autT := (φ x).2
  have hxO : Φ x ∉ omegaT := by
    intro h
    obtain ⟨s, hs⟩ := hrange _ h
    exact hxT (hΦinj hs ▸ s.2)
  have hx3' : ∃ k : ℕ, Φ x ^ 3 ^ k = 1 := by
    obtain ⟨k, hk⟩ := hx3
    exact ⟨k, by rw [← map_pow, hk, map_one]⟩
  have hxz' : Φ x * Φ z = Φ z * Φ x := by rw [← map_mul, ← map_mul, hxz]
  obtain ⟨U', hU'2, hU'O, hU'C, hU'N, h9⟩ := outer_criterion hzO hzo hxA hxO hx3' hxz'
  have hU'R : U' ≤ Φ.range := by
    intro w hw
    obtain ⟨s, hs⟩ := hrange w (hU'O hw)
    exact ⟨s, hs⟩
  refine ⟨U'.comap Φ, hU'2.comap_of_injective Φ hΦinj, ?_, ?_, ?_⟩
  · intro u hu
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 (hU'C hu)
    apply hΦinj
    rw [map_mul, map_mul]
    exact h1
  · rw [Subgroup.mem_normalizer_iff]
    intro u
    rw [Subgroup.mem_comap, Subgroup.mem_comap, map_mul, map_mul, map_inv]
    exact Subgroup.mem_normalizer_iff.1 hU'N (Φ u)
  · intro hd
    have hmap : (⁅U'.comap Φ, Subgroup.zpowers x⁆).map Φ = ⁅U', Subgroup.zpowers (Φ x)⁆ := by
      rw [Subgroup.map_commutator, Subgroup.map_comap_eq, inf_eq_right.mpr hU'R,
        MonoidHom.map_zpowers]
    have hcard : Nat.card ↥⁅U'.comap Φ, Subgroup.zpowers x⁆ =
        Nat.card ↥⁅U', Subgroup.zpowers (Φ x)⁆ := by
      rw [← hmap, Subgroup.card_map_of_injective hΦinj]
    have := Nat.le_of_dvd (by norm_num) hd
    omega

theorem frameExitD42_proved : FrameExitD42 :=
  frameExitD42_of_outerCommutator d42OuterCommutator_proved

end Exit

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.D42
