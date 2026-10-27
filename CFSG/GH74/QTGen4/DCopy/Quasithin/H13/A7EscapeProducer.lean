module

public import CFSG.Quasithin.H13.A7EscapeProducer
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A7Coordinates
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A7Escape
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A7EscapeLocal
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A7KLocal
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A7Offender
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A7EscapeLocalS331
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A7NaturalLocal

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.A7

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.SteinbergCB CFSG.Blueprint
open scoped Pointwise commutatorElement

@[expose] def StmtA7EscapingLocalActionData_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → QuasithinUnique.quasithinIsQTKECat G →
    quasithinIsSylowTwo T → ¬ QT13Excluded G →
    quasithinIsMaximalLocal T L → quasithinIsFaithfulLocal T L →
    CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) →
    Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ center (↥L ⧸ CFSG.pCore 2 ↥L) ≃*
      alternatingGroup (Fin 7)) →
    ∃ (e : G) (Y K D : Subgroup G) (v : G),
      e ∈ T ∧ (∀ t ∈ T, t * e = e * t) ∧ orderOf e = 2 ∧
      T ≤ Y ∧ Y ≤ centralizer ({e} : Set G) ∧ K ≤ Y ∧ D ≤ Y ∧
      ¬ K ≤ normalizer (L : Set G) ∧ D = ⁅D, thompsonJ T⁆ ∧
      v ≠ 1 ∧ v ∈ ⁅quasithinOmegaOneCenter T, D⁆ ∧
      centralizer ({v} : Set G) ≤ normalizer (L : Set G) ∧
      ∃ ρ : Y →* Perm (Fin 5) × Perm (Fin 3), Function.Surjective ρ ∧
        ρ.ker = (centralizer (VZ T Y : Set G)).subgroupOf Y ∧
        (K.subgroupOf Y).map ρ = (alternatingGroup (Fin 5)).prod ⊥ ∧
        (D.subgroupOf Y).map ρ = (⊥ : Subgroup (Perm (Fin 5))).prod (alternatingGroup (Fin 3))

theorem A7_escaping_local_action_data_of_hyp1223_F4
    (h12213 : Stmt12_2_13_F4) (h1227 : Stmt12_2_7_F4)
    (h1228 : Stmt12_2_8_F4) (h1229 : Stmt12_2_9_F4) (h331 : Stmt3_3_1_F4) {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]
    {T L V : Subgroup G} {ψ₀ : V ≃* Multiplicative (evenWeight 7)} (hyp : Hyp1223 G T L V)
    (hcfg₀ : A7NatConfig T L V ψ₀)
    (hA7 : Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ center (↥L ⧸ CFSG.pCore 2 ↥L) ≃*
      alternatingGroup (Fin 7))) :
    ∃ (e : G) (Y K D : Subgroup G) (v : G),
      e ∈ T ∧ (∀ t ∈ T, t * e = e * t) ∧ orderOf e = 2 ∧
      T ≤ Y ∧ Y ≤ centralizer ({e} : Set G) ∧ K ≤ Y ∧ D ≤ Y ∧
      ¬ K ≤ normalizer (L : Set G) ∧ D = ⁅D, thompsonJ T⁆ ∧
      v ≠ 1 ∧ v ∈ ⁅quasithinOmegaOneCenter T, D⁆ ∧
      centralizer ({v} : Set G) ≤ normalizer (L : Set G) ∧
      ∃ ρ : Y →* Perm (Fin 5) × Perm (Fin 3), Function.Surjective ρ ∧
        ρ.ker = (centralizer (VZ T Y : Set G)).subgroupOf Y ∧
        (K.subgroupOf Y).map ρ = (alternatingGroup (Fin 5)).prod ⊥ ∧
        (D.subgroupOf Y).map ρ =
          (⊥ : Subgroup (Perm (Fin 5))).prod (alternatingGroup (Fin 3)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs := hyp.simple
  have hnab := hyp.nonabelian
  have hQTKE := hyp.qtke
  have hT := hyp.sylow
  have hLmax := hyp.maximal
  have hLf := hyp.faithful
  have hLq := hyp.quasisimple
  obtain ⟨Ts, rfl⟩ : ∃ Ts : Sylow 2 G, (Ts : Subgroup G) = T :=
    ⟨_, IsPGroup.toSylow_coe hT.1 hT.2⟩

  obtain ⟨ψ, h, hTalign⟩ := hcfg₀.exists_aligned hT
  have hTL : (Ts : Subgroup G) ≤ normalizer (L : Set G) := hyp.normalizes
  set Z := quasithinOmegaOneCenter (Ts : Subgroup G) with hZdef
  have hTP' : ∀ t ∈ (Ts : Subgroup G), ∃ σ ∈ sevenP, IsCoordAct ψ t σ := by
    intro t ht
    obtain ⟨σ, hσ⟩ := h.Nact t (h.T_le ht)
    exact ⟨σ, ((hTalign σ).1 ⟨t, ht, hσ⟩).1, hσ⟩
  have hTP : ∀ t ∈ (Ts : Subgroup G), ∃ u, IsCoordAct ψ t (sevenWord u) := by
    intro t ht
    obtain ⟨σ, hσP, hσ⟩ := hTP' t ht
    obtain ⟨u, rfl⟩ := exists_word_of_mem_sevenP hσP
    exact ⟨u, hσ⟩

  obtain ⟨e, he⟩ := exists_vec_eq ψ vecFour_mem
  obtain ⟨e₂, he₂⟩ := exists_vec_eq ψ vecTwo_mem
  have heZ : (e : G) ∈ Z := mem_omegaOneCenter_of_fixed h.le_T ψ hTP' h.T_le fun g hg => by
    rw [he]
    exact sevenP_fix hg (Or.inr rfl)
  have he₂Z : (e₂ : G) ∈ Z := mem_omegaOneCenter_of_fixed h.le_T ψ hTP' h.T_le fun g hg => by
    rw [he₂]
    exact sevenP_fix hg (Or.inl rfl)
  have hZT : Z ≤ Ts := (Subgroup.closure_le _).2 fun x hx => (mem_inf.1 hx.1).1
  have hZC : Z ≤ centralizer ((Ts : Subgroup G) : Set G) :=
    (Subgroup.closure_le _).2 fun x hx => (mem_inf.1 hx.1).2
  have heT : (e : G) ∈ (Ts : Subgroup G) := hZT heZ
  have heTc : ∀ t ∈ (Ts : Subgroup G), t * e = e * t := fun t ht =>
    mem_centralizer_iff.1 (hZC heZ) t ht
  have hTe : (Ts : Subgroup G) ≤ centralizer ({(e : G)} : Set G) := fun t ht =>
    mem_centralizer_singleton_iff.2 (heTc t ht)
  have he1 : (e : G) ≠ 1 := by
    intro h1
    have h2 : e = 1 := Subtype.ext h1
    rw [h2, vec_one] at he
    exact vecFour_ne_zero he.symm
  have he2 : orderOf (e : G) = 2 := by
    refine orderOf_eq_prime ?_ he1
    rw [pow_two]
    exact congrArg Subtype.val (sq_eq_one_of_vec ψ e)

  have hCZ : centralizer (Z : Set G) ≤ normalizer (L : Set G) := by
    have h6 : hammingNorm (vec ψ (e * e₂)) = 6 := by
      rw [vec_mul, he, he₂]
      exact hammingNorm_vecFour_add_vecTwo
    refine le_trans ?_ (h.wt26 (e * e₂) (Or.inr h6))
    exact centralizer_le (Set.singleton_subset_iff.2 (mul_mem heZ he₂Z))

  have hsolv := (A7_natural_local_produces_normalizer_and_solvable_confinement_F4 h331 hs hnab hQTKE
    Ts hLmax hLf hLq h.le_T h.L_le h.T_le ψ h.Lact h.Lonto h.Nact h.NM h.TI
    (fun v hv => h.wt26 v (Or.inl hv)) h.wt4).2.2.2.2.2.2.2

  obtain ⟨v₀, hv₀1, hv₀M⟩ := A7NatConfig.exists_escape_F4 h12213 hyp hA7
  have hesc : ¬ centralizer ({(e : G)} : Set G) ≤ normalizer (L : Set G) :=
    h.centralizer_not_le_of_weight_four hv₀1 hv₀M (by rw [he]; exact hammingNorm_vecFour)
  obtain ⟨H, hH, hHe, hHs⟩ := exists_hStar_le_centralizer Ts heT heTc he1 hsolv hesc
  obtain ⟨hLie, hKmax, -, hA5sum, hred, -⟩ :=
    A7_escape_oTwoUpper_local_F4 h1227 Ts hyp hCZ hH hHs hsolv
  set K := oTwoUpper H with hKdef
  obtain ⟨eK⟩ := CFSG.LocalAnalysis.ComponentInitial.PSL2_four_alternating_five_model _ hLie
  have hKH : K ≤ H := oTwoUpper_le H
  have hTH : (Ts : Subgroup G) ≤ H := hH.1.1
  have hTK : (Ts : Subgroup G) ≤ normalizer (K : Set G) := hTH.trans (le_normalizer_oTwoUpper H)
  have hKe : K ≤ centralizer ({(e : G)} : Set G) := hKH.trans hHe
  have hKq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) := by
    have hsimple : IsSimpleGroup (alternatingGroup (Fin 5)) :=
      alternatingGroup.isSimpleGroup (by simp)
    have := eK.isSimpleGroup
    refine (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup ?_).1
    obtain ⟨a, b, hab⟩ := alternating_five_nonabelian
    refine ⟨eK.symm a, eK.symm b, fun h1 => hab ?_⟩
    have h2 := congrArg eK h1
    simpa using h2
  have hCK := centralizer_le_normalizer_of_uniqueMax_F4 h331 hs hnab hQTKE Ts hKmax hKq hTK he2
    (sup_le hKe hTe)
  have hKM : ¬ K ≤ normalizer (L : Set G) := by
    intro hKM
    apply hH.2.1
    rw [← eq_oTwoUpper_sup_sylow Ts hTH]
    exact sup_le hKM hTL
  have hKZ : ¬ K ≤ centralizer (Z : Set G) := fun hKZ => hKM (hKZ.trans hCZ)

  obtain ⟨⟨k, hkK, hkN, hk3, hkO⟩, hnotn⟩ := exists_borel Ts hTK eK
  have hk1 : k ≠ 1 := fun h1 => hkO (h1 ▸ one_mem _)
  have hkM : k ∈ normalizer (L : Set G) :=
    normalizer_inf_le_of_hStar Ts hH hKH hTK hnotn ⟨hKH hkK, hkN⟩
  have hkL : k ∈ L := mem_of_three_element_F4 h1228 hyp hA7 hkM hk3 hk1
  have hke : k ∈ centralizer ({(e : G)} : Set G) := hKe hkK
  have hkZ : ∀ z ∈ Z, k * z * k⁻¹ = z := fun z hz =>
    borel_centralizes Ts hTH hKH hTK hred hA5sum hkK hkN hk3 hz
  have hC2 := isPGroup_inf_centralizer h hLq he hCK eK hkK hkL hke hk3 hkO

  obtain ⟨p, o, hkl⟩ : ∃ p o, IsCoordAct ψ k (tcyc p o) := by
    set σ := (h.lamA ⟨k, hkL⟩ : Perm (Fin 7)) with hσdef
    have hσ := h.lamA_spec ⟨k, hkL⟩
    have hstab : permAct7 σ vecFour = vecFour :=
      (h.mem_centralizer_iff_lamA he ⟨k, hkL⟩).1 hke
    have h3 : ∀ i, σ (σ (σ i)) = i := by
      intro i
      have h1 : σ ^ 3 = 1 := by
        rw [hσdef, ← Subgroup.coe_pow, ← map_pow]
        have h2 : (⟨k, hkL⟩ : L) ^ 3 = 1 := Subtype.ext (by simpa using hk3)
        rw [h2, map_one]
        rfl
      have h2 := congrArg (fun τ : Perm (Fin 7) => τ i) h1
      simpa [pow_succ, Perm.mul_apply] using h2
    obtain ⟨a, j, hσeq⟩ := exists_fam27 ⟨hstab, h3⟩
    have hfix2 : permAct7 σ vecTwo = vecTwo := by
      have h1 := hσ e₂ e₂ (by
        show (e₂ : G) = k * e₂ * k⁻¹
        rw [hkZ _ he₂Z])
      rw [he₂] at h1
      exact h1.symm
    rw [hσeq] at hfix2
    have hj := fam27_fix_vecTwo a j hfix2
    subst hj
    rw [fam27_zero] at hσeq
    rcases a with _ | ⟨p, o⟩
    · exfalso
      have h1 : h.lamA ⟨k, hkL⟩ = 1 := Subtype.ext hσeq
      rw [h.lamA_eq_one_iff] at h1
      obtain ⟨n, hn⟩ := hC2 ⟨k, mem_inf.2 ⟨hkL, h1⟩⟩
      have hn' : k ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
      have h4 : orderOf k ∣ Nat.gcd 3 (2 ^ n) :=
        Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hk3) (orderOf_dvd_of_pow_eq_one hn')
      rw [show Nat.gcd 3 (2 ^ n) = 1 from Nat.Coprime.pow_right _ (by norm_num), Nat.dvd_one,
        orderOf_eq_one_iff] at h4
      exact hk1 h4
    · refine ⟨p, o, ?_⟩
      have h1 : σ = tcyc p o := hσeq
      rw [← h1]
      exact hσ

  obtain ⟨hall, j₀, hj₀J, hj₀l⟩ := h.exists_thompsonJ_swap01_F4 h1229 Ts hyp hCZ hTalign
  have hTall : ∀ u, ∃ t ∈ (Ts : Subgroup G), IsCoordAct ψ t (sevenWord u) := fun u =>
    (hTalign _).2 ⟨mem_sevenP_of_sevenCond (sevenCond_sevenWord u), hall _⟩
  obtain ⟨t₀, ht₀T, ht₀⟩ := (hTalign (swap 0 1)).2 ⟨swap01_mem_sevenP, hall _⟩
  obtain ⟨t₂, ht₂T, ht₂⟩ := (hTalign (swap 2 3)).2 ⟨swap23_mem_sevenP, hall _⟩

  obtain ⟨x, hxL, hxe, hxK, -, i, hi, hxl⟩ := h.exists_x hC2 hTL he hTe eK hCK ht₀T ht₀ hTall
    hkK hkL hke hk3 hkO hkl
  have hJT : thompsonJ (Ts : Subgroup G) ≤ Ts := iSup₂_le fun A hA => hA.1
  obtain ⟨D, hDJ, -, hDL, hDe, hDK, hDN, hDc, d₀, hd₀, i₀, hi₀, hd₀l⟩ :=
    h.exists_D hTL hTe eK hCK hTP hJT hj₀J hj₀l hxL hxe hxK hi hxl

  have ht₂K : sign (kAct eK ⟨t₂, hCK (hTe ht₂T)⟩) = -1 := by
    have hwL : t₂ * k * t₂⁻¹ * k ∈ L := mul_mem ((mem_normalizer_iff.1 (hTL ht₂T) k).1 hkL) hkL
    have hwC : (t₂ * k * t₂⁻¹ * k) ^ 2 ∈ centralizer (V : Set G) := by
      have ht₂N := h.T_le ht₂T
      have hkN' := h.L_le hkL
      have hw2N : (t₂ * k * t₂⁻¹ * k) ^ 2 ∈ normalizer (V : Set G) := h.L_le (pow_mem hwL 2)
      have h1 : h.lamN ⟨(t₂ * k * t₂⁻¹ * k) ^ 2, hw2N⟩ = 1 := by
        rw [show (⟨(t₂ * k * t₂⁻¹ * k) ^ 2, hw2N⟩ : normalizer (V : Set G)) =
          (⟨t₂, ht₂N⟩ * ⟨k, hkN'⟩ * ⟨t₂, ht₂N⟩⁻¹ * ⟨k, hkN'⟩) ^ 2 from rfl, map_pow, map_mul,
          map_mul, map_mul, map_inv, h.lamN_eq _ ht₂, h.lamN_eq _ hkl, swap_inv]
        exact swap23_tcyc_sq p o
      exact (h.lamN_eq_one_iff _).1 h1
    obtain ⟨n, hn⟩ := hC2 ⟨_, mem_inf.2 ⟨pow_mem hwL 2, hwC⟩⟩
    have hn' : ((t₂ * k * t₂⁻¹ * k) ^ 2) ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    refine sign_kAct_of_inverts Ts hTK eK hkK hkN hk3 hkO ht₂T ⟨n + 1, ?_⟩
    rw [pow_succ', pow_mul]
    exact hn'

  obtain ⟨ρ, hρs, hρker, hρK, hρD⟩ := h.exists_rho Ts hTL hC2 hTP hTe eK hCK hKZ he₂ he₂Z hDL
    hDe hDK hDN hDc hd₀ hi₀ hd₀l ht₀T ht₀ ht₂T ht₂ ht₂K

  have hd₀N : d₀ ∈ normalizer (V : Set G) := hDN hd₀
  have hconj : d₀ * (e₂ : G)⁻¹ * d₀⁻¹ ∈ V := (mem_normalizer_iff.1 hd₀N _).1 (inv_mem e₂.2)
  have hvV : ⁅(e₂ : G), d₀⁆ ∈ V := by
    rw [commutatorElement_def, mul_assoc (e₂ : G), mul_assoc (e₂ : G)]
    exact mul_mem e₂.2 hconj
  set v : V := ⟨⁅(e₂ : G), d₀⁆, hvV⟩ with hvdef
  have hvec : vec ψ v = vecTwo + permAct7 (cyc016 ^ (i₀ : ℕ)) vecTwo := by
    have h1 : v = e₂ * ⟨d₀ * (e₂ : G)⁻¹ * d₀⁻¹, hconj⟩ := Subtype.ext (by
      show ⁅(e₂ : G), d₀⁆ = (e₂ : G) * (d₀ * (e₂ : G)⁻¹ * d₀⁻¹)
      rw [commutatorElement_def]
      group)
    have h2 := hd₀l e₂⁻¹ ⟨d₀ * (e₂ : G)⁻¹ * d₀⁻¹, hconj⟩ (by simp)
    rw [h1, vec_mul, h2, vec_inv, he₂]
  have hv2 : hammingNorm (vec ψ v) = 2 := by
    rw [hvec]
    exact hammingNorm_vecTwo_add i₀ hi₀
  have hv1 : (v : G) ≠ 1 := by
    intro h1
    have h2 : v = 1 := Subtype.ext h1
    rw [h2, vec_one] at hv2
    simp at hv2
  refine ⟨e, (D ⊔ (Ts : Subgroup G)) ⊔ K, K, D, ⁅(e₂ : G), d₀⁆, heT, heTc, he2,
    le_sup_right.trans le_sup_left, sup_le (sup_le hDe hTe) hKe, le_sup_right,
    le_sup_left.trans le_sup_left, hKM, hDJ, hv1, commutator_mem_commutator he₂Z hd₀,
    h.wt26 v (Or.inl hv2), ρ, hρs, hρker, hρK, hρD⟩

theorem A7_escaping_local_action_data_producer_F4
    (hG10 : StmtA7NaturalModuleConfig_F4)
    (h12213 : Stmt12_2_13_F4) (h1227 : Stmt12_2_7_F4) (h1228 : Stmt12_2_8_F4) (h1229 : Stmt12_2_9_F4)
    (h331 : Stmt3_3_1_F4) : StmtA7EscapingLocalActionData_F4 := by
  intro G _ _ T L hs hnab hQTKE hT hnex hLmax hLf hLq hA7
  obtain ⟨V, ψ₀, hcfg₀⟩ := hG10 G T L hs hnab hQTKE hT hnex hLmax hLf hLq hA7
  exact A7_escaping_local_action_data_of_hyp1223_F4 h12213 h1227 h1228 h1229 h331
    (hcfg₀.hyp1223 hs hnab hQTKE hT hnex hLmax hLf hLq) hcfg₀ hA7

end CFSG.Quasithin.H13.A7
