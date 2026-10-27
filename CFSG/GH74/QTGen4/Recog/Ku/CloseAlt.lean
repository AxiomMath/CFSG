module

public import CFSG.GH74.QTGen4.Recog.Ku.CloseAltB
public import CFSG.Quasithin.Recognition.HSTypeS5Rec

public section

namespace CFSG.GH74.QTGen4.Ku

open CFSG.Open CFSG.GorensteinWalter CFSG.Quasithin.I4 CFSG.Quasithin.HSType

theorem dihedral_two_r_one_sq : (DihedralGroup.r 1 : DihedralGroup 2) ^ 2 = 1 := by
  decide

theorem dihedral_two_r_one_ne : (DihedralGroup.r 1 : DihedralGroup 2) ≠ 1 := by
  decide

theorem dihedral_two_sr_sq : (DihedralGroup.sr 0 : DihedralGroup 2) ^ 2 = 1 := by
  decide

theorem dihedral_two_sr_ne : (DihedralGroup.sr 0 : DihedralGroup 2) ≠ 1 := by
  decide

theorem dihedral_two_rsr_sq :
    ((DihedralGroup.r 1 : DihedralGroup 2) * DihedralGroup.sr 0) ^ 2 = 1 := by
  decide

theorem dihedral_two_rsr_ne :
    (DihedralGroup.r 1 : DihedralGroup 2) * DihedralGroup.sr 0 ≠ 1 := by
  decide

theorem orderOf_coe_of_dihedral {C : Type*} [Group C] (D : Subgroup C) (eD : D ≃* DihedralGroup 2)
    (x : D) (hx : orderOf (eD x) = 2) : orderOf (x : C) = 2 := by
  rw [Subgroup.orderOf_coe, ← MulEquiv.orderOf_eq eD, hx]

theorem exists_klein_pair {C : Type*} [Group C] (D : Subgroup C) (eD : D ≃* DihedralGroup 2) :
    ∃ z e : C, z ∈ D ∧ orderOf z = 2 ∧ orderOf e = 2 ∧ orderOf (z * e) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hr : orderOf (DihedralGroup.r 1 : DihedralGroup 2) = 2 :=
    orderOf_eq_prime dihedral_two_r_one_sq dihedral_two_r_one_ne
  have hs : orderOf (DihedralGroup.sr 0 : DihedralGroup 2) = 2 :=
    orderOf_eq_prime dihedral_two_sr_sq dihedral_two_sr_ne
  have hrs : orderOf ((DihedralGroup.r 1 : DihedralGroup 2) * DihedralGroup.sr 0) = 2 :=
    orderOf_eq_prime dihedral_two_rsr_sq dihedral_two_rsr_ne
  refine ⟨((eD.symm (DihedralGroup.r 1) : D) : C), ((eD.symm (DihedralGroup.sr 0) : D) : C),
    (eD.symm (DihedralGroup.r 1) : D).2, ?_, ?_, ?_⟩
  · exact orderOf_coe_of_dihedral D eD _ (by rw [MulEquiv.apply_symm_apply]; exact hr)
  · exact orderOf_coe_of_dihedral D eD _ (by rw [MulEquiv.apply_symm_apply]; exact hs)
  · rw [← Subgroup.coe_mul]
    exact orderOf_coe_of_dihedral D eD _ (by
      rw [map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]; exact hrs)

theorem pPrimeCore_eq_bot_of_klein {C : Type*} [Group C] [Finite C] {z e : C}
    (hz : orderOf z = 2) (he : orderOf e = 2) (hze : orderOf (z * e) = 2)
    (hcen : ∀ i : C, orderOf i = 2 → Nat.card (Subgroup.centralizer ({i} : Set C)) = 4) :
    pPrimeCore 2 C = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKi : ∀ i : C, orderOf i = 2 →
      pPrimeCore 2 C ⊓ Subgroup.centralizer ({i} : Set C) = ⊥ := by
    intro i hi
    obtain ⟨k, hk⟩ : ∃ k, Nat.card (Subgroup.centralizer ({i} : Set C)) = 2 ^ k :=
      ⟨2, by rw [hcen i hi]; norm_num⟩
    refine disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard ?_)
    rw [hk]
    exact Nat.Coprime.pow_right k (pPrimeCore_coprime_card (p := 2) (G := C)).symm
  exact eq_bot_of_inf_centralizer_eq_bot_three hz he (hKi z hz) (hKi e he) (hKi (z * e) hze)

theorem centralizer_normal_eq_bot {C : Type*} [Group C] [Finite C] {L : Subgroup C} [L.Normal]
    (hO : pPrimeCore 2 C = ⊥)
    (hcen : ∀ i : C, orderOf i = 2 → Nat.card (Subgroup.centralizer ({i} : Set C)) = 4)
    (hL : ¬ Nat.card L ∣ 4) :
    ∀ c : C, (∀ l ∈ L, c * l = l * c) → c = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := Subgroup.centralizer (L : Set C) with hN
  have hNn : N.Normal := ⟨fun n hn g => Subgroup.mem_centralizer_iff.mpr fun l hl => by
    have hl' : g⁻¹ * l * g ∈ L := by
      have := (inferInstance : L.Normal).conj_mem l hl g⁻¹
      rwa [inv_inv] at this
    have := Subgroup.mem_centralizer_iff.mp hn _ hl'
    calc l * (g * n * g⁻¹) = g * ((g⁻¹ * l * g) * n) * g⁻¹ := by group
      _ = g * (n * (g⁻¹ * l * g)) * g⁻¹ := by rw [this]
      _ = g * n * g⁻¹ * l := by group⟩
  have hNodd : Nat.Coprime 2 (Nat.card N) := by
    by_contra hcop
    have h2 : 2 ∣ Nat.card N := (Nat.Prime.dvd_iff_not_coprime Nat.prime_two).mpr hcop
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := ↥N) 2 h2
    have hu' : orderOf (u : C) = 2 := by rw [Subgroup.orderOf_coe, hu]
    have hLu : L ≤ Subgroup.centralizer ({(u : C)} : Set C) := fun l hl =>
      Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp u.2 l hl)
    have h4 := Subgroup.card_dvd_of_le hLu
    rw [hcen _ hu'] at h4
    exact hL h4
  have hNbot : N = ⊥ := by
    have hle : N ≤ pPrimeCore 2 C := le_sSup ⟨hNn, hNodd⟩
    rw [hO] at hle
    exact eq_bot_iff.mpr hle
  intro c hc
  have : c ∈ N := Subgroup.mem_centralizer_iff.mpr fun l hl => (hc l hl).symm
  rw [hNbot, Subgroup.mem_bot] at this
  exact this

theorem q_and_centralizer_of_dvd_four (K : Type) [Field K] [Finite K] {p f : ℕ} [Fact p.Prime]
    (hK : Nat.card K = p ^ f) (hp : Odd p) (hf : 0 < f) {t : PSL2 K} (ht : orderOf t = 2)
    (hc : Nat.card (Subgroup.centralizer ({t} : Set (PSL2 K))) ∣ 4) :
    Nat.card (Subgroup.centralizer ({t} : Set (PSL2 K))) = 4 ∧
      (Nat.card K = 3 ∨ Nat.card K = 5) := by
  have hp2 : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
  have hq2 : 2 ≤ p ^ f := le_trans hp2 (Nat.le_self_pow (by omega) p)
  have h4 : p ^ f % 4 = 1 ∨ p ^ f % 4 = 3 := by
    have := Nat.odd_iff.mp (hp.pow (n := f))
    omega
  rw [hK]
  rcases h4 with h4 | h4
  · have h := ((CFSG.Walter.psl2_centralizer_involution K hK hp hf ht).1 h4).1
    rw [h] at hc ⊢
    have hle : p ^ f - 1 ≤ 4 := Nat.le_of_dvd (by norm_num) hc
    generalize p ^ f = q at h4 hq2 hle ⊢
    constructor <;> omega
  · have h := ((CFSG.Walter.psl2_centralizer_involution K hK hp hf ht).2 h4).1
    rw [h] at hc ⊢
    have hle : p ^ f + 1 ≤ 4 := Nat.le_of_dvd (by norm_num) hc
    generalize p ^ f = q at h4 hq2 hle ⊢
    constructor <;> omega

theorem equiv_alt_of_range {C : Type*} [Group C] {n : ℕ} (θ : C →* Equiv.Perm (Fin n))
    (hθ : Function.Injective θ) (hr : θ.range = alternatingGroup (Fin n)) :
    Nonempty (C ≃* alternatingGroup (Fin n)) := by
  have hmem : ∀ c : C, θ c ∈ alternatingGroup (Fin n) := fun c => by
    rw [← hr]
    exact ⟨c, rfl⟩
  let φ : C →* alternatingGroup (Fin n) :=
    { toFun := fun c => ⟨θ c, hmem c⟩
      map_one' := Subtype.ext θ.map_one
      map_mul' := fun a b => Subtype.ext (θ.map_mul a b) }
  refine ⟨MulEquiv.ofBijective φ ⟨fun a b h => hθ (congrArg Subtype.val h), fun y => ?_⟩⟩
  have hy : (y : Equiv.Perm (Fin n)) ∈ θ.range := by
    rw [hr]
    exact y.2
  obtain ⟨c, hc⟩ := hy
  exact ⟨c, Subtype.ext hc⟩

theorem alt_four_or_five_of_klein
    {C : Type} [Group C] [Finite C] (D : Sylow 2 C)
    (eD : (D : Subgroup C) ≃* DihedralGroup 2)
    (hcen : ∀ i : C, orderOf i = 2 → Nat.card ↥(Subgroup.centralizer ({i} : Set C)) = 4)
    {w : C} (hw : orderOf w = 3) :
    Nonempty (C ≃* alternatingGroup (Fin 4)) ∨ Nonempty (C ≃* alternatingGroup (Fin 5)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdih : HasDihedralSylowTwo C := hasDihedralSylowTwo_of_sylow D (by norm_num) eD
  have hcardD : Nat.card (D : Subgroup C) = 4 :=
    (Nat.card_congr eD.toEquiv).trans DihedralGroup.nat_card
  have h8 : ¬ 8 ∣ Nat.card C := not_eight_dvd_card D hcardD
  obtain ⟨z, e, -, hz, he, hze⟩ := exists_klein_pair (D : Subgroup C) eD
  have hO : pPrimeCore 2 C = ⊥ := pPrimeCore_eq_bot_of_klein hz he hze hcen
  let eQ : C ⧸ pPrimeCore 2 C ≃* C :=
    (QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot
  rcases gorensteinWalter C hdih with ⟨-, hTwo⟩ | ⟨-, ⟨h7⟩⟩ |
      ⟨-, K, hK, L, hLn, -, hLmodel⟩
  ·
    exfalso
    obtain ⟨k, hk⟩ := (hTwo.of_equiv eQ) w
    have h3 := orderOf_dvd_of_pow_eq_one hk
    rw [hw] at h3
    exact absurd (Nat.prime_three.dvd_of_dvd_pow h3) (by norm_num)
  ·
    exfalso
    let f7 : C ≃* alternatingGroup (Fin 7) := eQ.symm.trans h7
    have hfz : orderOf (f7 z) = 2 := by rw [MulEquiv.orderOf_eq, hz]
    obtain ⟨g, hg⟩ := aSeven_involutions_conjugate (f7 z) a7t
      (isInvolution_of_orderOf_eq_two hfz) a7t_involution
    have h24 : (24 : ℕ) = 4 := by
      rw [← a7t_centralizer_card, ← hg]
      change Nat.card (Subgroup.centralizer {(MulAut.conj g) (f7 z)}) = 4
      rw [card_centralizer_map, card_centralizer_map, hcen z hz]
    norm_num at h24
  ·
    obtain ⟨p, fexp, hp, hpodd, hf0, hKcard⟩ := hK
    have : Fact p.Prime := ⟨hp⟩
    have hqodd : Odd (Nat.card K) := hKcard ▸ hpodd.pow
    have : L.Normal := hLn
    set L' : Subgroup C := L.map eQ.toMonoidHom with hL'def
    have hL'n : L'.Normal := hLn.map eQ.toMonoidHom eQ.surjective
    let eL : L' ≃* L := (L.equivMapOfInjective eQ.toMonoidHom eQ.injective).symm
    have hK' : IsOddPrimePower (Nat.card K) := ⟨p, fexp, hp, hpodd, hf0, hKcard⟩
    rcases hLmodel with hPSL | hPGL
    ·
      obtain ⟨ePSL⟩ := hPSL
      let eP : L' ≃* PSL2 K := eL.trans ePSL
      have hcardL' : Nat.card L' = Nat.card K * (Nat.card K ^ 2 - 1) / 2 :=
        (Nat.card_congr eP.toEquiv).trans (psl2_card_formula K hK')
      have h2L : 2 ∣ Nat.card L' := by
        obtain ⟨m, hm⟩ := eight_dvd_odd_mul (Nat.card K) hqodd
        rw [hcardL', hm]
        exact ⟨2 * m, by omega⟩
      obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := ↥L') 2 h2L
      have hu2 : orderOf (eP u) = 2 := by rw [MulEquiv.orderOf_eq, hu]
      have hu2C : orderOf (u : C) = 2 := by rw [Subgroup.orderOf_coe, hu]
      have hcC : Nat.card (Subgroup.centralizer ({eP u} : Set (PSL2 K))) =
          Nat.card ↥(L' ⊓ Subgroup.centralizer ({(u : C)} : Set C)) := by
        rw [card_centralizer_map]
        exact card_centralizer_subtype L' u.2
      have hd4 : Nat.card ↥(L' ⊓ Subgroup.centralizer ({(u : C)} : Set C)) ∣ 4 := by
        have := Subgroup.card_dvd_of_le
          (inf_le_right : L' ⊓ Subgroup.centralizer ({(u : C)} : Set C) ≤
            Subgroup.centralizer ({(u : C)} : Set C))
        rw [hcen _ hu2C] at this
        exact this
      obtain ⟨-, hq⟩ := q_and_centralizer_of_dvd_four K hKcard hpodd hf0 hu2
        (by rw [hcC]; exact hd4)
      have hcardL'' : Nat.card L' = 12 ∨ Nat.card L' = 60 := by
        rw [hcardL']
        rcases hq with h | h <;> rw [h] <;> norm_num
      have hL : ¬ Nat.card L' ∣ 4 := by
        rcases hcardL'' with h | h <;> rw [h] <;> norm_num
      have : L'.Normal := hL'n
      have hCL : ∀ c : C, (∀ l ∈ L', c * l = l * c) → c = 1 :=
        centralizer_normal_eq_bot hO hcen hL
      rcases hq with h3' | h5'
      ·
        left
        let : Fintype K := Fintype.ofFinite K
        obtain ⟨e3⟩ := nonempty_psl2_equiv_zmod (K := K) Nat.prime_three
          (by rw [← Nat.card_eq_fintype_card, h3'])
        let eA : L' ≃* ↥(alternatingGroup (Fin 4)) :=
          (eP.trans e3).trans psl2_three_equiv_alternatingGroup
        obtain ⟨θ, hθ, hθL⟩ := exists_embedding_of_alt eA alt_four_aut_conj
          (fun ρ hρ => eq_one_of_comm_alt_four ρ ⟨hρ _ aA4_mem, hρ _ bA4_mem⟩) hCL
        have hA : alternatingGroup (Fin 4) ≤ θ.range := fun σ hσ => by
          obtain ⟨l, hl⟩ := eA.surjective ⟨σ, hσ⟩
          exact ⟨l, by rw [hθL, hl]⟩
        have hA12 : Nat.card (alternatingGroup (Fin 4)) = 12 := by
          rw [Nat.card_eq_fintype_card, card_alternatingGroup]
          decide
        have hrange := range_eq_alt θ hθ hA
          (by rw [hA12, Nat.card_perm, Nat.card_fin]; decide) h8
          (by rw [hA12]; decide)
        exact equiv_alt_of_range θ hθ hrange
      ·
        right
        obtain ⟨⟨e5⟩, -⟩ := CFSG.LinearGroups.five_field_linear_two_alternating_five_model K h5'
        let eA : L' ≃* ↥(alternatingGroup (Fin 5)) := eP.trans e5
        obtain ⟨θ, hθ, hθL⟩ := exists_embedding_of_alt eA alt_five_aut_conj
          (fun ρ hρ => eq_one_of_comm_alt_five ρ ⟨hρ _ aA5_mem, hρ _ bA5_mem⟩) hCL
        have hA : alternatingGroup (Fin 5) ≤ θ.range := fun σ hσ => by
          obtain ⟨l, hl⟩ := eA.surjective ⟨σ, hσ⟩
          exact ⟨l, by rw [hθL, hl]⟩
        have hA60 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
          rw [Nat.card_eq_fintype_card, card_alternatingGroup]
          decide
        have hrange := range_eq_alt θ hθ hA
          (by rw [hA60, Nat.card_perm, Nat.card_fin]; decide) h8
          (by rw [hA60]; decide)
        exact equiv_alt_of_range θ hθ hrange
    ·
      exfalso
      obtain ⟨ePGL⟩ := hPGL
      let eP : L' ≃* PGL2 K := eL.trans ePGL
      have hcardL' : Nat.card L' = Nat.card K * (Nat.card K ^ 2 - 1) :=
        (Nat.card_congr eP.toEquiv).trans (pgl2_card_formula K)
      have h8L : 8 ∣ Nat.card L' := by
        rw [hcardL']
        exact eight_dvd_odd_mul (Nat.card K) hqodd
      exact h8 (dvd_trans h8L (Subgroup.card_subgroup_dvd_card L'))

end CFSG.GH74.QTGen4.Ku
