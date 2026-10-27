module

public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialTorusInvolution

public section

namespace CFSG.Semidihedral.FixedCoreNontrivial

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.Semidihedral.StationaryConfinement
  (stationary_all_local_prime_covers_confine_every_nontrivial_odd_core_element)

theorem trivial_fixed_core_torus_normalizer_structure
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (hrecognition : PerfectLayerNormalization.OriginalSmallerSimpleRecognition G)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (t : G)
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 9 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (hcov : EscapingLocalEigensubgroups.allLocalPrimeStationaryCovers t (fS (s n) : G))
    (hY : (((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).index = 2)
    (hA₀ : (N t).map (C t).subtype ⊓ Subgroup.centralizer {(fS (s n) : G)} = ⊥)
    (hN : N t ≠ ⊥) :
    let q : ℕ := p ^ f
    let e : ℤ := if q % 4 = 1 then 1 else -1
    let s₀ : G := fS (s n)
    let V : Subgroup G := Subgroup.zpowers t ⊔ Subgroup.zpowers s₀
    let D : Subgroup G := Subgroup.centralizer (V : Set G)
    let W : Subgroup G := (CFSG.pPrimeCore 2 D).map D.subtype
    let B : Subgroup G := (N t).map (C t).subtype
    let H : Subgroup G := Subgroup.normalizer (W : Set G)
    let K : Subgroup G := Subgroup.centralizer (W : Set G)
    IsCyclic W ∧ (Nat.card W : ℤ) = ((q : ℤ) + e) / 2 ∧ V ⊔ W = D ∧ Disjoint V W ∧
      B ≤ K ∧ K.relIndex H = 2 ∧ (∀ h ∈ H, h ∉ K → ∀ w ∈ W, h * w * h⁻¹ = w⁻¹) ∧
      (CFSG.pPrimeCore 2 H).map H.subtype = W ∧ (CFSG.pPrimeCore 2 K).map K.subtype = W ∧
      (∃ P : Sylow 2 K, (P : Subgroup K).map K.subtype = V) ∧
      (∀ W₀ : Subgroup G, W₀ ≤ W → W₀ ≠ ⊥ → Subgroup.normalizer (W₀ : Set G) = H) ∧
      (∀ w ∈ W, w ≠ 1 → Subgroup.centralizer {w} = K) ∧
      ∃ d : G, d ∈ C t ∧ orderOf d = 4 ∧ d ^ 2 = t ∧ d * s₀ * d⁻¹ = t * s₀ ∧
        (∀ w ∈ W, d * w * d⁻¹ = w⁻¹) ∧ (∀ x ∈ B, d * x = x * d) ∧
        (∃ P : Sylow 2 H, (P : Subgroup H).map H.subtype =
          Subgroup.zpowers d ⊔ Subgroup.zpowers s₀) ∧
        C t ⊓ H = W ⊔ B ⊔ (Subgroup.zpowers d ⊔ Subgroup.zpowers s₀) ∧
        ∃ (F' : Type) (_ : Field F') (_ : Finite F')
          (φ : H ⧸ CFSG.pPrimeCore 2 H ≃* CFSG.GorensteinWalter.PGL2 F'),
          (Nat.card F' % 8 = 3 ∨ Nat.card F' % 8 = 5) ∧
          ((K.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore 2 H))).map φ.toMonoidHom =
            (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F')).range ∧
          let q' : ℕ := Nat.card F'
          let e' : ℤ := if q' % 4 = 1 then 1 else -1
          4 * (Nat.card B : ℤ) = q' - e' ∧
          let v : G := s₀ * d
          let X : Subgroup G := H ⊓ Subgroup.centralizer {v}
          let U : Subgroup G := (CFSG.pPrimeCore 2 X).map X.subtype
          orderOf v = 2 ∧ v ∈ H ∧ v ∉ K ∧ IsCyclic U ∧ 2 * (Nat.card U : ℤ) = q' + e' ∧
            U ≤ K ∧ (∀ u ∈ U, t * u * t⁻¹ = u⁻¹) ∧ Nat.Coprime (Nat.card U) (Nat.card B) := by
  intro q e s₀ V D W B H K
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hzt, ht2, -, hsC, hs2, hst⟩ := Principal.supplied_t_s_facts hn fS ht
  have hq5' : 5 < p ^ f := by omega
  obtain ⟨J, d, hL, -, -, hDV, hWcard⟩ := trivial_fixed_core_local_data G hGnonab hrecognition n
    hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel hcov hY hA₀
  have hWodd : Odd (Nat.card W) := by
    rw [Subgroup.card_map_of_injective D.subtype_injective]
    exact Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := D))
  have hBodd : Odd (Nat.card B) := by
    rw [Subgroup.card_map_of_injective (C t).subtype_injective]
    exact Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := C t))
  have hW1 : W ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card W = 1 := by rw [hbot]; exact Subgroup.card_bot
    rw [hWcard] at h1
    split_ifs at h1 <;> omega
  have hBne : B ≠ ⊥ := by
    intro hbot
    exact hN ((Subgroup.map_eq_bot_iff_of_injective _ (C t).subtype_injective).mp hbot)
  have hV : IsKleinFour V := Principal.supplied_four_group_isKleinFour hn fS ht
  have htV : t ∈ V := Subgroup.mem_sup_left (Subgroup.mem_zpowers t)
  have hsV : s₀ ∈ V := Subgroup.mem_sup_right (Subgroup.mem_zpowers s₀)
  have hVp : IsPGroup 2 V := IsPGroup.of_card (n := 2) (by rw [hV.card_four]; norm_num)
  have hdisj : Disjoint V W := by
    rw [Subgroup.disjoint_def]
    intro x hxV hxW
    exact eq_one_of_mem_of_odd hVp hxV (hL.W_odd x hxW)
  have hconf : ∀ u ∈ B, u ≠ 1 →
      Subgroup.centralizer ({u} : Set G) ≤ Subgroup.centralizer ({t} : Set G) :=
    (stationary_all_local_prime_covers_confine_every_nontrivial_odd_core_element
      G hGnonab hrecognition n hn S fS t s₀ ht2 hs2 hsC (fun h => hst h.symm) hnonab hcentral hnc
      p f hp hpodd hf hq5' hmodel hcov).2.1
  have hSC : (S : Subgroup G) ≤ Subgroup.centralizer {t} := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff, ← hzt]
    have h := (Subgroup.mem_center_iff.mp (CFSG.Semidihedral.z_mem_center n hn))
      (fS.symm ⟨x, hx⟩)
    have h' := congrArg (fun w => ((fS w : S) : G)) h
    simpa only [map_mul, Subgroup.coe_mul, MulEquiv.apply_symm_apply] using h'
  have hS4 : ∀ x ∈ (S : Subgroup G), orderOf x = 4 → x ^ 2 = t := by
    intro x hx hx4
    have hy : orderOf (fS.symm ⟨x, hx⟩) = 4 := by
      rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
      exact hx4
    have h := congrArg (fun w => ((fS w : S) : G))
      (semidihedral_order_four_square n hn _ hy)
    simpa only [map_pow, Subgroup.coe_pow, MulEquiv.apply_symm_apply, hzt] using h
  have htS : t ∈ (S : Subgroup G) := by
    rw [ht]
    exact Subgroup.pow_mem _ (fS (r n)).property _
  have hVS : V ≤ (S : Subgroup G) :=
    sup_le (Subgroup.zpowers_le.mpr htS) (Subgroup.zpowers_le.mpr (fS (s n)).property)
  have : Group.IsPerfect G := Principal.isPerfect_of_isSimpleGroup hGnonab
  have hsurj : Function.Surjective V.normalizerMonoidHom := MonoidHom.range_eq_top.mp
    ((CFSG.Semidihedral.Local.perfect_semidihedral_full_local_fusion n hn S fS).1 V hVS hV).1
  obtain ⟨a, ha, b, hb, hgt, hgs⟩ := exists_commutator_three_cycle hV htV hsV hL.t_ne_one
    hL.s_ne_one hL.s_ne.symm hsurj
  have hWcomm : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := hL.W_comm
  obtain ⟨-, -, -, hoddW, -⟩ := Principal.klein_centralizer_odd_core V W hV hWodd hWcomm hDV hdisj
  have hMH : ∀ c ∈ Subgroup.normalizer (V : Set G), c ∈ Subgroup.normalizer (W : Set G) := by
    intro c hc
    apply mem_normalizer_of_conj_mem
    intro w hw
    have hcD := mem_normalizer_centralizer hc
    apply hoddW _ ((Subgroup.mem_normalizer_iff.mp hcD w).mp
      ((show W ≤ Subgroup.centralizer (V : Set G) from hDV ▸ le_sup_right) hw))
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hL.W_odd w hw
  have hgW := commutator_mem_centralizer_of_isCyclic hL.W_cyclic (hMH a ha) (hMH b hb)
  obtain ⟨-, hKH2, hinvH, hdK, hOH, hOK, hVSyl, hNW₀, hCw, hPH, hCH, F', hF', hF'fin, φ, hF'K,
    hmod, hpsl⟩ := hL.torus_normalizer hV hWodd hW1 hDV hconf hgt hgs hgW S hSC hS4
  have hVK : V ≤ K :=
    Subgroup.le_centralizer_iff.mpr (show W ≤ Subgroup.centralizer (V : Set G) from
      hDV ▸ le_sup_right)
  obtain ⟨hq'3, h4B, hvo, hvH, hvK, hUcyc, h2U, hUK, htinv, hcop⟩ := hL.torus_involutions hWodd
    hBodd hW1 hBne hgt hgW hVK hKH2 hinvH hdK hOH F' φ hF'K hmod hpsl
  refine ⟨hL.W_cyclic, ?_, hDV, hdisj, hL.B_le_centralizer_W, hKH2, hinvH, hOH, hOK, hVSyl, hNW₀,
    hCw, d, hL.d_mem_C, hL.d_orderOf, by rw [pow_two]; exact hL.d_sq, hL.d_s, hL.d_inv,
    fun x hx => hL.JB_comm d hL.d_mem x hx, hPH, hCH, F', hF', hF'fin, φ, hmod, hpsl hq'3, h4B,
    hvo, hvH, hvK, hUcyc, h2U, hUK, htinv, hcop⟩
  rw [hWcard]
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (by positivity)
  show (((if p ^ f % 4 = 1 then p ^ f + 1 else p ^ f - 1) / 2 : ℕ) : ℤ) =
    ((p ^ f : ℕ) + (if p ^ f % 4 = 1 then (1 : ℤ) else -1)) / 2
  split_ifs with h
  · push_cast
    rfl
  · push_cast [show 1 ≤ p ^ f from hq1]
    ring_nf

end CFSG.Semidihedral.FixedCoreNontrivial
