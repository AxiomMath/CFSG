module

public import CFSG.GH74.GLS.IVK.A7.Glue
public import CFSG.GH74.KGroups.TwoA7Cover

public section

namespace CFSG.GH74.KGroups.TwoA7

open CFSG.ClassicalInvolution.Hat2A7 Equiv

theorem four_le_card_centralizer_dihedral (c : DihedralGroup 4) (hc : c * c = 1) :
    4 ≤ Nat.card ↥(Subgroup.centralizer ({c} : Set (DihedralGroup 4))) := by
  have hdec : ∀ c : DihedralGroup 4, c * c = 1 →
      4 ≤ (Finset.univ.filter (fun y : DihedralGroup 4 => y * c = c * y)).card := by decide
  have h1 := hdec c hc
  have h2 : Nat.card ↥(Subgroup.centralizer ({c} : Set (DihedralGroup 4))) =
      (Finset.univ.filter (fun y : DihedralGroup 4 => y * c = c * y)).card := by
    have h3 : ((Subgroup.centralizer ({c} : Set (DihedralGroup 4)) : Subgroup (DihedralGroup 4)) :
        Set (DihedralGroup 4)) =
        ↑(Finset.univ.filter (fun y : DihedralGroup 4 => y * c = c * y)) := by
      ext y
      simp [Subgroup.mem_centralizer_singleton_iff]
    show Nat.card ((Subgroup.centralizer ({c} : Set (DihedralGroup 4)) :
      Subgroup (DihedralGroup 4)) : Set (DihedralGroup 4)) = _
    rw [h3]
    exact Nat.card_eq_finsetCard _
  omega

theorem exists_four_le_centralizer_of_dihedral {G : Type*} [Group G] (Y : Subgroup G)
    (e : ↥Y ≃* DihedralGroup 4) {d : G} (hdY : d ∈ Y) (hd2 : d * d = 1) :
    ∃ C : Subgroup G, C ≤ Y ∧ 4 ≤ Nat.card ↥C ∧ ∀ x ∈ C, x * d = d * x := by
  obtain ⟨c, hc⟩ : ∃ c : DihedralGroup 4, c = e ⟨d, hdY⟩ := ⟨_, rfl⟩
  have hc2 : c * c = 1 := by
    rw [hc, ← map_mul, ← map_one e]
    congr 1
    exact Subtype.ext hd2
  let ι : DihedralGroup 4 →* G := Y.subtype.comp e.symm.toMonoidHom
  have hι : Function.Injective ι := Y.subtype_injective.comp e.symm.injective
  have hιc : ι c = d := by
    show ((e.symm c : ↥Y) : G) = d
    rw [hc, MulEquiv.symm_apply_apply]
  refine ⟨(Subgroup.centralizer ({c} : Set (DihedralGroup 4))).map ι, ?_, ?_, ?_⟩
  · rintro _ ⟨k, -, rfl⟩
    exact (e.symm k).2
  · rw [Subgroup.card_map_of_injective hι]
    exact four_le_card_centralizer_dihedral c hc2
  · rintro _ ⟨k, hk, rfl⟩
    have hkc := Subgroup.mem_centralizer_singleton_iff.1 hk
    rw [← hιc, ← map_mul, ← map_mul, hkc]

theorem four_le_card_centralizer_of_normalized {D : Subgroup (Perm (Fin 7))} {σ : Perm (Fin 7)}
    (hDA : D ≤ alternatingGroup (Fin 7)) (hD8 : Nat.card D = 8)
    (hσ2 : σ * σ = 1) (hσodd : σ ∉ alternatingGroup (Fin 7))
    (hnorm : ∀ d ∈ D, σ * d * σ⁻¹ ∈ D) :
    4 ≤ Nat.card ↥(D ⊓ Subgroup.centralizer ({σ} : Set (Perm (Fin 7)))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hσ1 : σ ≠ 1 := fun h => hσodd (h ▸ (alternatingGroup (Fin 7)).one_mem)
  have hσsign : Equiv.Perm.sign σ = -1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
    · exact absurd (Equiv.Perm.mem_alternatingGroup.mpr h) hσodd
    · exact h
  have hσinv : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hσ2
  have hord : orderOf σ = 2 := orderOf_eq_prime (by rw [pow_two]; exact hσ2) hσ1
  have hzp : Nat.card ↥(Subgroup.zpowers σ) = 2 := by rw [Nat.card_zpowers, hord]
  have hσN : σ ∈ Subgroup.normalizer (D : Set (Perm (Fin 7))) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨hnorm x, fun hx => ?_⟩
    have h1 := hnorm _ hx
    have h2 : σ * (σ * x * σ⁻¹) * σ⁻¹ = x := by
      rw [hσinv]
      calc σ * (σ * x * σ) * σ = (σ * σ) * x * (σ * σ) := by group
        _ = x := by rw [hσ2]; group
    rwa [h2] at h1
  have hpow : ∀ n : ℤ, σ ^ n = 1 ∨ σ ^ n = σ := by
    intro n
    rw [← zpow_mod_orderOf, hord, Nat.cast_ofNat]
    rcases Int.emod_two_eq_zero_or_one n with hk | hk
    · left; rw [hk]; simp
    · right; rw [hk]; simp
  have hdisj : Disjoint D (Subgroup.zpowers σ) := by
    rw [Subgroup.disjoint_def]
    intro x hxD hxz
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxz
    rcases hpow n with h1 | h1
    · exact h1
    · exact absurd (hDA (h1 ▸ hxD)) hσodd
  have hcardT : Nat.card ↥(D ⊔ Subgroup.zpowers σ) =
      2 ^ (Nat.card (Perm (Fin 7))).factorization 2 := by
    have h4 : (Nat.card (Perm (Fin 7))).factorization 2 = 4 :=
      CFSG.GH74.GLS.IVK.A7.factorization_S7
    rw [CFSG.GH74.GLS.IVK.A7.card_sup_of_le_normalizer' D _ ((Subgroup.zpowers_le).2 hσN) hdisj,
      hD8, hzp, h4]
    norm_num
  let T : Sylow 2 (Perm (Fin 7)) := Sylow.ofCard (D ⊔ Subgroup.zpowers σ) hcardT
  have hTcoe : (T : Subgroup (Perm (Fin 7))) = D ⊔ Subgroup.zpowers σ := rfl
  obtain ⟨f, hf2, hfcyc, hfT, -, hfcomm, -⟩ := CFSG.GH74.GLS.IVK.ivk_1_1T T
  obtain ⟨k, hk8, -, ⟨eY⟩⟩ := CFSG.GH74.GLS.IVK.ivk_1_1a T
  have hk4 : k = 4 := by omega
  subst hk4
  have hDY : D ≤ (T : Subgroup (Perm (Fin 7))) ⊓ alternatingGroup (Fin 7) :=
    le_inf (by rw [hTcoe]; exact le_sup_left) hDA
  have hcardY : Nat.card ↥((T : Subgroup (Perm (Fin 7))) ⊓ alternatingGroup (Fin 7)) = 8 := by
    rw [Nat.card_congr eY.toEquiv, DihedralGroup.nat_card]
  have hDeqY : D = (T : Subgroup (Perm (Fin 7))) ⊓ alternatingGroup (Fin 7) :=
    Subgroup.eq_of_le_of_card_ge hDY (by rw [hcardY, hD8])
  have hf2' : f * f = 1 := by
    have := pow_orderOf_eq_one f
    rwa [hf2, pow_two] at this
  have hfsign : Equiv.Perm.sign f = -1 := by
    rw [Equiv.Perm.sign_of_cycleType, hfcyc]
    simp only [Multiset.sum_singleton, Multiset.card_singleton]
    exact Odd.neg_one_pow (by decide)
  have hσT : σ ∈ (T : Subgroup (Perm (Fin 7))) := by
    rw [hTcoe]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers σ)
  obtain ⟨d0, hd0⟩ : ∃ d0 : Perm (Fin 7), d0 = f * σ := ⟨_, rfl⟩
  have hd0T : d0 ∈ (T : Subgroup (Perm (Fin 7))) := hd0 ▸ Subgroup.mul_mem _ hfT hσT
  have hd0A : d0 ∈ alternatingGroup (Fin 7) := by
    rw [Equiv.Perm.mem_alternatingGroup, hd0, map_mul, hfsign, hσsign]
    rfl
  have hd0Y : d0 ∈ (T : Subgroup (Perm (Fin 7))) ⊓ alternatingGroup (Fin 7) := ⟨hd0T, hd0A⟩
  have hfd0 : d0 * f = f * d0 := hfcomm d0 hd0Y
  have hσfd0 : σ = f * d0 := by rw [hd0, ← mul_assoc, hf2', one_mul]
  have hd02 : d0 * d0 = 1 := by
    calc d0 * d0 = (f * f) * (d0 * d0) := by rw [hf2', one_mul]
      _ = f * (f * d0) * d0 := by group
      _ = f * (d0 * f) * d0 := by rw [hfd0]
      _ = (f * d0) * (f * d0) := by group
      _ = σ * σ := by rw [← hσfd0]
      _ = 1 := hσ2
  obtain ⟨C, hCY, hC4, hCd0⟩ :=
    exists_four_le_centralizer_of_dihedral _ eY hd0Y hd02
  have hCle : C ≤ D ⊓ Subgroup.centralizer ({σ} : Set (Perm (Fin 7))) := by
    intro x hx
    refine ⟨by rw [hDeqY]; exact hCY hx, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    have hxf : x * f = f * x := hfcomm x (hCY hx)
    have hxd : x * d0 = d0 * x := hCd0 x hx
    rw [hσfd0]
    calc x * (f * d0) = (x * f) * d0 := by group
      _ = f * (x * d0) := by rw [hxf]; group
      _ = f * (d0 * x) := by rw [hxd]
      _ = (f * d0) * x := by group
  exact hC4.trans (Subgroup.card_le_of_le hCle)

section Four

variable {E : Type} [Group E] [Finite E] {π : E →* A7} {z : E}

theorem twoA7_exists_orderOf_four
    (h : IsDoubleCoverA7 π z) {R : Subgroup E}
    (hRord : ∀ x ∈ R, orderOf x ∣ 16) (hR : 4 ≤ Nat.card R) : ∃ y ∈ R, orderOf y = 4 := by
  have hex : ∃ x ∈ R, 4 ∣ orderOf x := by
    by_contra hcon
    push Not at hcon
    have hle : R ≤ Subgroup.zpowers z := by
      intro x hx
      have hx2 : x * x = 1 := by
        obtain ⟨m, -, hmx⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
          (show orderOf x ∣ 2 ^ 4 by simpa using hRord x hx)
        have hm1 : m ≤ 1 := by
          by_contra hm1
          push Not at hm1
          exact hcon x hx (by rw [hmx]; exact (pow_dvd_pow 2 hm1 : 2 ^ 2 ∣ 2 ^ m))
        have h1 := pow_orderOf_eq_one x
        rw [hmx] at h1
        interval_cases m
        · have hx1 : x = 1 := by simpa using h1
          rw [hx1, one_mul]
        · simpa [pow_two] using h1
      rcases h.eq_one_or_eq_z_of_sq_eq_one hx2 with h1 | h1
      · rw [h1]; exact Subgroup.one_mem _
      · rw [h1]; exact Subgroup.mem_zpowers z
    have h2 := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, orderOf_z h] at h2
    omega
  obtain ⟨x, hxR, hx4⟩ := hex
  have hx0 : orderOf x ≠ 0 := (orderOf_pos x).ne'
  have hpos : 0 < orderOf x / 4 :=
    Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hx0) hx4) (by norm_num)
  refine ⟨x ^ (orderOf x / 4), R.pow_mem hxR _, ?_⟩
  rw [orderOf_pow_of_dvd hpos.ne' (Nat.div_dvd_of_dvd hx4), Nat.div_div_self hx4 hx0]

theorem four_fixed
    (h : IsDoubleCoverA7 π z) (φ : MulAut E) (hφ2 : φ * φ = 1)
    (hout : φ ∉ CFSG.GH74.GLS.Stage1.Thm2.Recip.innOf E) (P : Subgroup E)
    (hP : CFSG.GH74.GLS.Stage1.Thm6.IsSylow2In P ⊤) (hinv : ∀ p ∈ P, φ p ∈ P) :
    ∃ y ∈ P, orderOf y = 4 ∧ φ y = y := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hP2, hPidx⟩ := hP
  let P' : Sylow 2 E := hP2.toSylow (by rwa [← Subgroup.relIndex_top_right])
  have hPcard : Nat.card P = 16 := h.card_sylow P'
  have hzP : z ∈ P := by
    have hdvd : 2 ∣ Nat.card P := by rw [hPcard]; norm_num
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := P) 2 hdvd
    have hx' : orderOf (x : E) = 2 := by rw [Subgroup.orderOf_coe]; exact hx
    have hx2 : (x : E) * x = 1 := by
      have := pow_orderOf_eq_one (x : E)
      rwa [hx', pow_two] at this
    rcases h.eq_one_or_eq_z_of_sq_eq_one hx2 with h1 | h1
    · rw [h1, orderOf_one] at hx'
      omega
    · rw [← h1]
      exact x.2
  have hkerP : π.ker ≤ P := by
    rw [ker_eq_zpowers h, Subgroup.zpowers_le]
    exact hzP
  obtain ⟨σ, hσdef⟩ : ∃ σ : Perm (Fin 7), σ = h.autPerm φ := ⟨_, rfl⟩
  have hσ2 : σ * σ = 1 := by rw [hσdef, ← map_mul, hφ2, map_one]
  have hσodd : σ ∉ alternatingGroup (Fin 7) := by
    intro hσ
    obtain ⟨q, hq⟩ := h.surjective ⟨σ, hσ⟩
    apply hout
    have h1 : h.autPerm (MulAut.conj q) = σ := by rw [autPerm_conj h q, hq]
    have h2 : MulAut.conj q = φ := h.autPerm_injective (h1.trans hσdef)
    rw [← h2]
    exact ⟨q, rfl⟩
  have hDAcard : Nat.card ↥(P.map π) = 8 := by
    have h1 := CFSG.ClassicalInvolution.QuaternionStructure.natCard_comap_eq π h.surjective
      (P.map π)
    rw [Subgroup.comap_map_eq, sup_eq_left.mpr hkerP, h.card_ker, hPcard] at h1
    omega
  obtain ⟨D, hD⟩ : ∃ D : Subgroup (Perm (Fin 7)),
      D = (P.map π).map (alternatingGroup (Fin 7)).subtype := ⟨_, rfl⟩
  have hDle : D ≤ alternatingGroup (Fin 7) := by
    rw [hD]
    rintro _ ⟨d, -, rfl⟩
    exact d.2
  have hD8 : Nat.card D = 8 := by
    rw [hD, Subgroup.card_map_of_injective (alternatingGroup (Fin 7)).subtype_injective, hDAcard]
  have hnorm : ∀ d ∈ D, σ * d * σ⁻¹ ∈ D := by
    intro d hd
    rw [hD] at hd ⊢
    obtain ⟨a, ha, rfl⟩ := hd
    obtain ⟨p, hp, rfl⟩ := ha
    exact ⟨π (φ p), ⟨φ p, hinv p hp, rfl⟩, by rw [hσdef]; exact h.autPerm_spec φ p⟩
  have hCD := four_le_card_centralizer_of_normalized hDle hD8 hσ2 hσodd hnorm
  obtain ⟨CD, hCDdef⟩ : ∃ CD : Subgroup (Perm (Fin 7)),
      CD = D ⊓ Subgroup.centralizer ({σ} : Set (Perm (Fin 7))) := ⟨_, rfl⟩
  have hCDle : CD ≤ alternatingGroup (Fin 7) := by
    rw [hCDdef]
    exact inf_le_left.trans hDle
  have hCD4 : 4 ≤ Nat.card CD := by
    rw [hCDdef]
    exact hCD
  have hHcard : Nat.card ↥((CD.subgroupOf (alternatingGroup (Fin 7))).comap π) =
      2 * Nat.card CD := by
    have h1 := CFSG.ClassicalInvolution.QuaternionStructure.natCard_comap_eq π h.surjective
      (CD.subgroupOf (alternatingGroup (Fin 7)))
    have h2 : Nat.card ↥(CD.subgroupOf (alternatingGroup (Fin 7))) = Nat.card CD :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCDle).toEquiv
    rw [h2, h.card_ker] at h1
    exact h1
  have hmemH : ∀ x ∈ (CD.subgroupOf (alternatingGroup (Fin 7))).comap π,
      ((π x : A7) : Perm (Fin 7)) ∈ CD := fun x hx => hx
  have hHfix : ∀ x ∈ (CD.subgroupOf (alternatingGroup (Fin 7))).comap π, π (φ x) = π x := by
    intro x hx
    apply h.map_apply_eq_of_mem_evenCentralizer φ
    rw [mem_evenCentralizer, ← hσdef]
    have h1 := hmemH x hx
    rw [hCDdef] at h1
    exact Subgroup.mem_centralizer_singleton_iff.1 h1.2
  have hcard := h.card_le_two_mul_card_fixedIn φ _ hHfix
  have hR4 : 4 ≤ Nat.card ↥(fixedIn φ ((CD.subgroupOf (alternatingGroup (Fin 7))).comap π)) := by
    omega
  have hRP : ∀ x ∈ fixedIn φ ((CD.subgroupOf (alternatingGroup (Fin 7))).comap π), x ∈ P := by
    intro x hx
    have hxD : ((π x : A7) : Perm (Fin 7)) ∈ D := by
      have h1 := hmemH x (mem_fixedIn.1 hx).1
      rw [hCDdef] at h1
      exact h1.1
    rw [hD] at hxD
    obtain ⟨a, ha, hax⟩ := hxD
    have hax' : a = π x := Subtype.ext hax
    rw [hax'] at ha
    obtain ⟨p, hp, hpx⟩ := ha
    rcases h.eq_or_eq_mul_z_of_map_eq hpx.symm with h1 | h1
    · rw [h1]
      exact hp
    · rw [h1]
      exact P.mul_mem hp hzP
  have hRord : ∀ x ∈ fixedIn φ ((CD.subgroupOf (alternatingGroup (Fin 7))).comap π),
      orderOf x ∣ 16 := fun x hx => by
    have := Subgroup.orderOf_dvd_natCard P (hRP x hx)
    rwa [hPcard] at this
  obtain ⟨y, hyR, hy4⟩ := twoA7_exists_orderOf_four h hRord hR4
  exact ⟨y, hRP y hyR, hy4, (mem_fixedIn.1 hyR).2⟩

end Four

end CFSG.GH74.KGroups.TwoA7
