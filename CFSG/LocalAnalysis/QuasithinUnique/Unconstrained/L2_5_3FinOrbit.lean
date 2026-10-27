module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_3FinBasic
public import CFSG.LocalAnalysis.QuasithinUnique.EscapingComponents
public import CFSG.Quasithin.Background.A3Structure39Aut

public section

namespace CFSG.QuasithinUnique.Fin253

open CFSG.Open CFSG.Quasithin

section Generic

variable {G : Type} [Group G] [Finite G]

theorem le_centralizer_of_component {H R L K' Q : Subgroup G} (hLH : L ≤ H)
    (hLperf : Group.IsPerfect ↥L) (hK' : IsComponentIn K' H)
    (hLR : ∀ l ∈ L, ∀ r ∈ R, l * r = r * l) (hQR : Q ≤ R) (hQK : Q ≤ K')
    (hQnc : ∃ q ∈ Q, ∃ k ∈ K', q * k ≠ k * q)
    (hsolv : Group.IsSolvable ↥(K' ⊓ Subgroup.centralizer (Q : Set G)))
    (hout : OutSolvable ↥K') : L ≤ Subgroup.centralizer (K' : Set G) := by
  have hnorm : L ≤ Subgroup.normalizer (K' : Set G) := by
    intro l hl
    have hK'' : IsComponentIn (CFSG.conjugate K' l) H :=
      Unc25G2.isComponentIn_conjugate hK' (hLH hl)
    rcases BenderBranch.eq_or_commute_of_isComponentIn hK' hK'' with h | h
    · exact BenderBranch.conjugate_eq_iff_mem_normalizer.mp h.symm
    · exfalso
      obtain ⟨q, hq, k, hk, hqk⟩ := hQnc
      have hqK'' : q ∈ CFSG.conjugate K' l := by
        rw [BenderBranch.mem_conjugate_iff]
        have e : l * q * l⁻¹ = q := by rw [hLR l hl q (hQR hq)]; group
        rw [e]
        exact hQK hq
      exact hqk (BenderBranch.commute_of_commutator_eq_bot h hk hqK'').symm
  let ψ : ↥L →* MulAut ↥K' :=
    (Subgroup.normalizerMonoidHom K').comp (Subgroup.inclusion hnorm)
  have hψ : ∀ (γ : ↥L) (k : ↥K'), ((ψ γ k : ↥K') : G) = (γ : G) * (k : G) * (γ : G)⁻¹ := by
    intro γ k
    simp [ψ]
  let C' : Subgroup ↥K' := (K' ⊓ Subgroup.centralizer (Q : Set G)).subgroupOf K'
  have hC'solv : Group.IsSolvable ↥C' := by
    have e : ↥C' ≃* ↥(K' ⊓ Subgroup.centralizer (Q : Set G)) :=
      Subgroup.subgroupOfEquivOfLe inf_le_left
    exact Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
  let SolG : Subgroup (MulAut ↥K') := C'.map (MulAut.conj : ↥K' →* MulAut ↥K')
  have hSolG : Group.IsSolvable ↥SolG :=
    Group.isSolvable_of_surjective (MonoidHom.subgroupMap_surjective _ C')
  have hrange : ∀ γ : ↥L, ψ γ ∈ SolG := by
    intro γ
    obtain ⟨x, hx⟩ := CFSG.Quasithin.A38.exists_inner_of_outSolvable hout hLperf ψ γ
    have hxC : x ∈ C' := by
      rw [Subgroup.mem_subgroupOf]
      refine ⟨x.2, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro q hq
      have h1 := congrArg (fun φ : MulAut ↥K' => ((φ ⟨q, hQK hq⟩ : ↥K') : G)) hx
      simp only [hψ, MulAut.conj_apply, Subgroup.coe_mul, InvMemClass.coe_inv] at h1
      have h2 : (γ : G) * q * (γ : G)⁻¹ = q := by rw [hLR γ γ.2 q (hQR hq)]; group
      rw [h2] at h1
      calc q * (x : G) = (x : G) * q * (x : G)⁻¹ * (x : G) := by rw [← h1]
        _ = (x : G) * q := by group
    rw [hx]
    exact Subgroup.mem_map_of_mem _ hxC
  let f : ↥L →* ↥SolG := ψ.codRestrict SolG hrange
  have hf : ∀ γ : ↥L, ψ γ = 1 := by
    intro γ
    have := eq_one_of_perfect_of_isSolvable hLperf f γ
    have h2 := congrArg Subtype.val this
    simpa [f] using h2
  intro l hl
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have h1 := congrArg (fun φ : MulAut ↥K' => ((φ ⟨k, hk⟩ : ↥K') : G)) (hf ⟨l, hl⟩)
  simp only [hψ] at h1
  have h2 : l * k * l⁻¹ = k := h1
  calc k * l = l * k * l⁻¹ * l := by rw [h2]
    _ = l * k := by group

theorem isComponentIn_of_orbit {H R D L : Subgroup G} {𝒦 : Set (Subgroup G)}
    (hHD : H ≤ Subgroup.normalizer (D : Set G)) (hRD : R ≤ D) (hR2 : IsPGroup 2 R) (hRH : R ≤ H)
    (hgen : ∀ l : G, (∀ K' ∈ 𝒦, ∀ k ∈ K', k * l = l * k) → ∀ d ∈ D, d * l = l * d)
    (hmem : ∀ K' ∈ 𝒦, IsComponentIn K' H ∧ ∃ Q : Subgroup G, Q ≤ R ∧ Q ≤ K' ∧
      (∃ q ∈ Q, ∃ k ∈ K', q * k ≠ k * q) ∧
      Group.IsSolvable ↥(K' ⊓ Subgroup.centralizer (Q : Set G)) ∧ OutSolvable ↥K')
    (hL : IsComponentIn L (H ⊓ Subgroup.normalizer (R : Set G))) : IsComponentIn L H := by
  set X : Subgroup G := H ⊓ Subgroup.normalizer (R : Set G) with hX
  have hLX : L ≤ X := hL.1
  have hLH : L ≤ H := hLX.trans inf_le_left
  have hLperf : Group.IsPerfect ↥L := (BenderBranch.isQuasisimple_of_isComponentIn hL).1
  have hRX : R ≤ pCoreOf 2 X :=
    le_pCoreOf_of_normal_pGroup (le_inf hRH Subgroup.le_normalizer) inf_le_right hR2
  have hLR : ∀ l ∈ L, ∀ r ∈ R, l * r = r * l := fun l hl r hr =>
    BenderBranch.commute_of_commutator_eq_bot (Unc25G2.commutator_pCoreOf_eq_bot hL) hl (hRX hr)
  have hLK : ∀ K' ∈ 𝒦, L ≤ Subgroup.centralizer (K' : Set G) := by
    intro K' hK'
    obtain ⟨hKc, Q, hQR, hQK, hQnc, hsolv, hout⟩ := hmem K' hK'
    exact le_centralizer_of_component hLH hLperf hKc hLR hQR hQK hQnc hsolv hout
  have hLD : L ≤ Subgroup.centralizer (D : Set G) := by
    intro l hl
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    exact hgen l (fun K' hK' k hk => Subgroup.mem_centralizer_iff.mp (hLK K' hK' hl) k hk) d hd
  set C : Subgroup G := H ⊓ Subgroup.centralizer (D : Set G) with hC
  have hCX : C ≤ X := fun c hc =>
    ⟨hc.1, Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le
      (SetLike.coe_subset_coe.mpr hRD) hc.2)⟩
  have hLC : L ≤ C := le_inf hLH hLD
  have hCnormal : (C.subgroupOf H).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left]
    exact CFSG.RankThreeCoreUniqueness.Helpers.common_normalizer_le_normalizer_inf H H _
      Subgroup.le_normalizer (hHD.trans (normalizer_le_normalizer_centralizer D))
  have hCsub : (C.subgroupOf H).IsSubnormal := hCnormal.isSubnormal
  have hLCsub : (L.subgroupOf C).IsSubnormal := subgroupOf_isSubnormal_of_le hCX hL.2.2
  have hLHsub : (L.subgroupOf H).IsSubnormal :=
    (subgroupOf_isSubnormal_iff hLC inf_le_left hCsub).mpr hLCsub
  exact isComponentIn_of_le_of_isSubnormal hL inf_le_left hLHsub

omit [Finite G] in
theorem conjJoin_map_conj {H K : Subgroup G} {g : G} (hg : g ∈ H) :
    conjJoin H (K.map (MulAut.conj g).toMonoidHom) = conjJoin H K := by
  apply le_antisymm
  · refine iSup_le fun h => ?_
    rw [Unc25G2.map_conj_conj]
    exact le_iSup (fun s : ↥H => K.map (MulAut.conj (s : G)).toMonoidHom)
      ⟨(h : G) * g, H.mul_mem h.2 hg⟩
  · refine iSup_le fun h => ?_
    have e : K.map (MulAut.conj (h : G)).toMonoidHom =
        (K.map (MulAut.conj g).toMonoidHom).map (MulAut.conj ((h : G) * g⁻¹)).toMonoidHom := by
      rw [Unc25G2.map_conj_conj, inv_mul_cancel_right]
    rw [e]
    exact le_iSup (fun s : ↥H => (K.map (MulAut.conj g).toMonoidHom).map
      (MulAut.conj (s : G)).toMonoidHom) ⟨(h : G) * g⁻¹, H.mul_mem h.2 (H.inv_mem hg)⟩

@[expose] def conjFamily (H K : Subgroup G) : Set (Subgroup G) :=
  {K' | ∃ g : ↥H, K' = K.map (MulAut.conj (g : G)).toMonoidHom}

omit [Finite G] in
theorem mem_conjFamily_isComponentIn {H K K' : Subgroup G} (hK : IsComponentIn K H)
    (hK' : K' ∈ conjFamily H K) : IsComponentIn K' H := by
  obtain ⟨g, rfl⟩ := hK'
  exact Unc25G2.isComponentIn_map_conj hK g.2

omit [Finite G] in
theorem conjFamily_gen {H K : Subgroup G} (l : G)
    (h : ∀ K' ∈ conjFamily H K, ∀ k ∈ K', k * l = l * k) :
    ∀ d ∈ conjJoin H K, d * l = l * d := by
  have hle : conjJoin H K ≤ Subgroup.centralizer ({l} : Set G) := by
    refine iSup_le fun g => fun x hx => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact h _ ⟨g, rfl⟩ x hx
  intro d hd
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hd)

end Generic

section Orbits

variable {G : Type} [Group G] [Finite G] {T M H S : Subgroup G} {z : G}

theorem charTwo_inf_component (hs : UnconstrainedSetting G T M) (ht : Tuple25 T M H S z)
    {K' : Subgroup G} (hK' : IsComponentIn K' H) : CharTwo (M ⊓ K') := by
  have hY : CharTwo (H ⊓ M) := ht.gamma0.charTwo_inf hs.setting ht.sylow_inf
  have hXY : M ⊓ K' ≤ H ⊓ M := fun x hx => ⟨hK'.1 hx.2, hx.1⟩
  have hsub : ((M ⊓ K').subgroupOf (H ⊓ M)).IsSubnormal := by
    have := hK'.2.2.comap (Subgroup.inclusion (inf_le_left : H ⊓ M ≤ H))
    convert this using 1
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.coe_inclusion,
      Subgroup.mem_inf]
    exact ⟨fun h => h.2, fun h => ⟨x.2.2, h⟩⟩
  exact EscapingComponents.charTwo_of_isSubnormal hY hXY hsub

theorem list_member_data (hs : UnconstrainedSetting G T M) (ht : Tuple25 T M H S z) {K' : Subgroup G}
    (hK' : IsComponentIn K' H) (hcl : ComponentList M S z K') :
    (∃ q ∈ pCoreOf 2 (M ⊓ K'), ∃ k ∈ K', q * k ≠ k * q) ∧
      Group.IsSolvable ↥(K' ⊓ Subgroup.centralizer (pCoreOf 2 (M ⊓ K') : Set G)) := by
  have hq : CFSG.IsQuasisimple ↥K' := BenderBranch.isQuasisimple_of_isComponentIn hK'
  have hQ2 : IsPGroup 2 (pCoreOf 2 (M ⊓ K')) :=
    CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 _
  have hQK : pCoreOf 2 (M ⊓ K') ≤ K' :=
    (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 _).trans inf_le_right
  obtain ⟨-, -, hcomm, -, hcase⟩ := hcl
  have hsyl : ∀ P : Subgroup G, IsSylowTwoOf P K' → P ≤ pCoreOf 2 (M ⊓ K') →
      (∃ q ∈ pCoreOf 2 (M ⊓ K'), ∃ k ∈ K', q * k ≠ k * q) ∧
        Group.IsSolvable ↥(K' ⊓ Subgroup.centralizer (pCoreOf 2 (M ⊓ K') : Set G)) := by
    intro P hP hPQ
    have hPQeq : pCoreOf 2 (M ⊓ K') = P := hP.eq_of_le hPQ hQK hQ2
    rw [hPQeq]
    refine ⟨?_, isSolvable_inf_centralizer_of_isSylowTwoOf hP⟩
    by_contra hcon
    push Not at hcon
    exact Unc25G2.false_of_isSylowTwoOf_le_centralizer hq hP fun q hqP =>
      Subgroup.mem_centralizer_iff.mpr fun k hk => (hcon q hqP k hk).symm
  rcases hcase with ⟨-, P, hP, hB⟩ | ⟨-, -, P, hP, hB⟩ | ⟨-, zL, hzL, hMK⟩ | ⟨-, hMK⟩
  · exact hsyl P hP (le_pCoreOf_of_normal_pGroup (by rw [hB]; exact le_inf hP.1 Subgroup.le_normalizer)
      (by rw [hB]; exact inf_le_right) hP.2.1)
  · exact hsyl P hP (le_pCoreOf_of_normal_pGroup (by rw [hB]; exact le_inf hP.1 Subgroup.le_normalizer)
      (by rw [hB]; exact inf_le_right) hP.2.1)
  ·
    obtain ⟨hzLK, hproj⟩ := hzL
    have hY2 : CharTwo (M ⊓ K') := charTwo_inf_component hs ht hK'
    have hcommY : ∀ y ∈ M ⊓ K', y * zL = zL * y := fun y hy => by
      rw [hMK] at hy
      exact Subgroup.mem_centralizer_singleton_iff.mp hy.2
    have hpowY : ∀ n : ℕ, zL ^ n ∈ M ⊓ K' := fun n => by
      rw [hMK]
      exact ⟨K'.pow_mem hzLK n, Subgroup.mem_centralizer_singleton_iff.mpr
        (Commute.pow_left (Commute.refl zL) n).eq⟩
    have hord : orderOf zL ≠ 0 := (orderOf_pos zL).ne'
    obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd hord
    have hbc : zL ^ 2 ^ k ∈ Subgroup.centralizer (pCoreOf 2 (M ⊓ K') : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hyY : y ∈ M ⊓ K' := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 _ hy
      exact (Commute.pow_right (show Commute y zL from hcommY y hyY) _).eq
    have hbQ : zL ^ 2 ^ k ∈ pCoreOf 2 (M ⊓ K') := hY2 ⟨hpowY _, hbc⟩
    obtain ⟨j, hj⟩ := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 (M ⊓ K')
      ⟨zL ^ 2 ^ k, hbQ⟩
    have hbj : (zL ^ 2 ^ k) ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    have hbm : (zL ^ 2 ^ k) ^ m = 1 := by
      rw [← pow_mul, ← hkm]
      exact pow_orderOf_eq_one zL
    have hcop : Nat.Coprime m (2 ^ j) :=
      Nat.Coprime.pow_right j ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr
        hm.not_two_dvd_nat).symm
    have h1 : orderOf (zL ^ 2 ^ k) ∣ 1 := by
      have := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hbm) (orderOf_dvd_of_pow_eq_one hbj)
      rwa [hcop.gcd_eq_one] at this
    have hb1 : zL ^ 2 ^ k = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1)
    have hp : IsPGroup 2 (Subgroup.zpowers zL) := by
      intro g
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp g.2
      refine ⟨k, Subtype.ext ?_⟩
      show (g : G) ^ 2 ^ k = 1
      rw [← hi, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hb1, one_zpow]
    have hle : Subgroup.zpowers zL ≤ M ⊓ K' := by
      rw [Subgroup.zpowers_le]
      simpa using hpowY 1
    have hn : M ⊓ K' ≤ Subgroup.normalizer ((Subgroup.zpowers zL : Subgroup G) : Set G) := by
      intro y hy
      refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun h hh => ?_)
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      exact (Commute.zpow_left (show Commute zL y from (hcommY y hy).symm) i).eq
    have hzQ : zL ∈ pCoreOf 2 (M ⊓ K') :=
      le_pCoreOf_of_normal_pGroup hle hn hp (Subgroup.mem_zpowers zL)
    refine ⟨⟨zL, hzQ, ?_⟩, ?_⟩
    ·
      by_contra hcon
      push Not at hcon
      have hz_cent : ∀ x ∈ K', z * x = x * z := by
        intro x hx
        have h1 := hproj x hx
        have h2 : zL⁻¹ * x * zL = x := by
          calc zL⁻¹ * x * zL = zL⁻¹ * (x * zL) := by rw [mul_assoc]
            _ = zL⁻¹ * (zL * x) := by rw [(hcon x hx).symm]
            _ = x := by rw [← mul_assoc, inv_mul_cancel, one_mul]
        have h3 : z⁻¹ * x * z = x := h1.trans h2
        calc z * x = z * (z⁻¹ * x * z) := by rw [h3]
          _ = x * z := by group
      have hKbot : K' = ⊥ := by
        calc K' = ⁅K', Subgroup.zpowers z⁆ := hcomm.symm
          _ = ⊥ := by
            refine Subgroup.commutator_eq_bot_iff_le_centralizer.mpr fun x hx => ?_
            refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
            obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
            exact (Commute.zpow_left (hz_cent x hx) i).eq
      exact Unc25G2.isComponentIn_ne_bot hK' hKbot
    ·
      have hle2 : K' ⊓ Subgroup.centralizer (pCoreOf 2 (M ⊓ K') : Set G) ≤ pCoreOf 2 (M ⊓ K') := by
        intro x hx
        have hxz : x * zL = zL * x := (Subgroup.mem_centralizer_iff.mp hx.2 zL hzQ).symm
        have hxY : x ∈ M ⊓ K' := by
          rw [hMK]
          exact ⟨hx.1, Subgroup.mem_centralizer_singleton_iff.mpr hxz⟩
        exact hY2 ⟨hxY, hx.2⟩
      have hP2 : IsPGroup 2 ↥(K' ⊓ Subgroup.centralizer (pCoreOf 2 (M ⊓ K') : Set G)) :=
        hQ2.to_le hle2
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have : Group.IsNilpotent ↥(K' ⊓ Subgroup.centralizer (pCoreOf 2 (M ⊓ K') : Set G)) :=
        hP2.isNilpotent
      infer_instance
  ·
    have hS' : IsSylowTwoOf (S ⊓ K') K' :=
      RankOneRecog.isSylowTwoOf_inf_of_subnormal ht.sylow hK'.1 hK'.2.2
    exact hsyl (S ⊓ K') hS' (le_pCoreOf_of_normal_pGroup (by rw [hMK])
      (by rw [hMK]; exact Subgroup.le_normalizer) hS'.2.1)

end Orbits

end CFSG.QuasithinUnique.Fin253
