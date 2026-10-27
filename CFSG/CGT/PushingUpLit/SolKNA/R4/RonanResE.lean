module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinD2Leaves2
public import CFSG.ClassicalInvolution.Q3.TL4LinkE2Hyp
public import CFSG.CGT.PushingUpLit.SolKNA.R4.RonanResOcta

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.ClassicalInvolution.Disconnected (DConnected dAdj DEdgeless)

section SetE

variable {X : Type} [Group X] [Finite X] {r : ℕ} {Φ : Set (Subgroup X)}

structure SetE (r : ℕ) (Φ : Set (Subgroup X)) : Prop where
  four_le : 4 ≤ r
  typeR : TypeRFam r Φ
  odd : classicalInvolutionOddCore X = ⊥
  inO2 : ∀ L ∈ Φ, ∀ u : X, IsUniqueInvolution L u →
    ∃ Q : Subgroup X, Q.Normal ∧ IsPGroup 2 Q ∧ u ∈ Q

namespace SetE

variable (h : SetE r Φ)
include h

theorem isPGroup {L : Subgroup X} (hL : L ∈ Φ) : IsPGroup 2 ↥L := by
  obtain ⟨u, hu⟩ := Sec6Gen.exists_uniqueInvolution h.typeR.hyp hL
  obtain ⟨Q, hQn, hQ2, huQ⟩ := h.inO2 L hL u hu
  exact LinkE2.isPGroup_of_inO2_typeR h.typeR h.odd hL hu hQn hQ2 huQ

theorem card_eq {L : Subgroup X} (hL : L ∈ Φ) : Nat.card ↥L = 2 ^ r := by
  obtain ⟨e⟩ := h.typeR.quat L hL L (AlphaFr.E2A.isSylow2In_self (h.isPGroup hL))
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  obtain ⟨k, hk⟩ : ∃ k, r = k + 2 := ⟨r - 2, by have := h.four_le; omega⟩
  rw [hk, Nat.add_sub_cancel, pow_add]
  ring

theorem sixteen_le {L : Subgroup X} (hL : L ∈ Φ) : 16 ≤ Nat.card ↥L := by
  rw [h.card_eq hL]
  calc 16 = 2 ^ 4 := by norm_num
    _ ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) h.four_le

theorem isQuatSub {L : Subgroup X} (hL : L ∈ Φ) : IsQuatSub L :=
  Sec6Gen.isQuatSub_of_mem_RSet h.typeR.hyp (TC.mem_RSet_of_isPGroup hL (h.isPGroup hL))

theorem aEmpty {L : Subgroup X} (hL : L ∈ Φ) : AEmpty Φ L :=
  aEmpty_of_noTwins h.typeR.hyp hL (h.typeR.noTwins L hL)

theorem normalizes {J L : Subgroup X} (hJ : J ∈ Φ) (hL : L ∈ Φ) {v : X}
    (hv : IsUniqueInvolution L v) : v ∈ Subgroup.normalizer (J : Set X) :=
  mem_normalizer_of_four_le h.four_le h.typeR.hyp (fun _ hJ => h.isPGroup hJ)
    (fun _ hJ => h.card_eq hJ) h.inO2 hJ hL hv

theorem exists_inv {L : Subgroup X} (hL : L ∈ Φ) : ∃ z, IsUniqueInvolution L z :=
  Sec6Gen.exists_uniqueInvolution h.typeR.hyp hL

theorem inv_ne {J K : Subgroup X} (hJ : J ∈ Φ) (hK : K ∈ Φ) (hne : J ≠ K) {zJ zK : X}
    (hzJ : IsUniqueInvolution J zJ) (hzK : IsUniqueInvolution K zK) : zJ ≠ zK := by
  intro e
  exact hne (h.typeR.noTwins K hK J ⟨hJ, zK, hzK, e ▸ hzJ⟩)

theorem inf_eq_bot {J K : Subgroup X} (hJ : J ∈ Φ) (hK : K ∈ Φ) (hne : J ≠ K) :
    J ⊓ K = ⊥ := by
  by_contra hbot
  obtain ⟨zJ, hzJ⟩ := h.exists_inv hJ
  obtain ⟨zK, hzK⟩ := h.exists_inv hK
  have hp : IsPGroup 2 ↥(J ⊓ K) := (h.isPGroup hJ).to_le inf_le_left
  have hcard : 2 ∣ Nat.card ↥(J ⊓ K) := by
    obtain ⟨k, hk⟩ := hp.exists_card_eq
    rcases k with _ | k
    · exfalso
      apply hbot
      rw [Nat.pow_zero] at hk
      exact (Subgroup.card_eq_one.mp hk)
    · rw [hk]
      exact ⟨2 ^ k, by ring⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := ↥(J ⊓ K)) 2 hcard
  have hc2 : orderOf (c : X) = 2 := by rw [Subgroup.orderOf_coe]; exact hc
  have hsq : (c : X) * (c : X) = 1 := by
    have := pow_orderOf_eq_one (c : X)
    rwa [hc2, pow_two] at this
  have hne1 : (c : X) ≠ 1 := by
    intro e
    rw [e, orderOf_one] at hc2
    omega
  have e1 : (c : X) = zJ := (hzJ.unique c c.2.1 hsq).resolve_left hne1
  have e2 : (c : X) = zK := (hzK.unique c c.2.2 hsq).resolve_left hne1
  exact h.inv_ne hJ hK hne hzJ hzK (e1.symm.trans e2)

end SetE

@[expose] def NC (J K : Subgroup X) : Prop := J ≠ K ∧ ¬ Commutes J K

theorem NC.symm {J K : Subgroup X} (h : NC J K) : NC K J :=
  ⟨h.1.symm, fun hc => h.2 hc.symm⟩

structure Cyc2 (K U : Subgroup X) : Prop where
  le : U ≤ K
  cyclic : IsCyclic ↥U
  card : Nat.card ↥K = 2 * Nat.card ↥U

namespace SetE

variable (h : SetE r Φ)
include h

theorem exists_cyc2 {K : Subgroup X} (hK : K ∈ Φ) : ∃ U, Cyc2 K U := by
  obtain ⟨U, hUK, hU, hc⟩ := (h.isQuatSub hK).exists_cyclic_index_two
  exact ⟨U, ⟨hUK, hU, hc⟩⟩

theorem cyc2_eq {K U U' : Subgroup X} (hK : K ∈ Φ) (hU : Cyc2 K U) (hU' : Cyc2 K U') : U = U' :=
  (h.isQuatSub hK).eq_of_cyclic hU.le hU'.le hU.cyclic hU'.cyclic hU.card hU'.card
    (h.sixteen_le hK)

theorem cyc2_mem_USet {K U : Subgroup X} (hK : K ∈ Φ) (hU : Cyc2 K U) : U ∈ USet Φ :=
  mem_USet_of_natCard hK (AlphaFr.E2A.isSylow2In_self (h.isPGroup hK)) hU.le hU.cyclic hU.card

theorem cyc2_comm {J K U V : Subgroup X} (hJ : J ∈ Φ) (hK : K ∈ Φ) (hU : Cyc2 J U)
    (hV : Cyc2 K V) {x y : X} (hx : x ∈ U) (hy : y ∈ V) : x * y = y * x := by
  by_cases hJK : J = K
  · subst hJK
    have := h.cyc2_eq hJ hU hV
    subst this
    exact AscL62.cyclic_comm hU.cyclic hx hy
  · have hUS := h.cyc2_mem_USet hJ hU
    have hVS := h.cyc2_mem_USet hK hV
    have h1 : U ≤ Subgroup.normalizer (V : Set X) :=
      le_normalizer_of_four_le h.four_le h.typeR.hyp (fun _ hJ => h.isPGroup hJ)
        (fun _ hJ => h.card_eq hJ) (fun _ hJ => h.aEmpty hJ) h.odd h.inO2 hVS hUS
    have h2 : V ≤ Subgroup.normalizer (U : Set X) :=
      le_normalizer_of_four_le h.four_le h.typeR.hyp (fun _ hJ => h.isPGroup hJ)
        (fun _ hJ => h.card_eq hJ) (fun _ hJ => h.aEmpty hJ) h.odd h.inO2 hUS hVS
    have hxV : x * y * x⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (h1 hx) y).mp hy
    have hyU : y * x⁻¹ * y⁻¹ ∈ U :=
      (Subgroup.mem_normalizer_iff.mp (h2 hy) x⁻¹).mp (U.inv_mem hx)
    have hcV : x * y * x⁻¹ * y⁻¹ ∈ V := V.mul_mem hxV (V.inv_mem hy)
    have hcU : x * y * x⁻¹ * y⁻¹ ∈ U := by
      have := U.mul_mem hx hyU
      simpa [mul_assoc] using this
    have hbot : x * y * x⁻¹ * y⁻¹ ∈ J ⊓ K := ⟨hU.le hcU, hV.le hcV⟩
    rw [h.inf_eq_bot hJ hK hJK, Subgroup.mem_bot] at hbot
    calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
      _ = y * x := by rw [hbot, one_mul]

theorem cyc2_le_normalizer {J K U : Subgroup X} (hJ : J ∈ Φ) (hK : K ∈ Φ) (hU : Cyc2 J U) :
    U ≤ Subgroup.normalizer (K : Set X) := by
  by_cases hJK : J = K
  · subst hJK
    exact hU.le.trans Subgroup.le_normalizer
  · obtain ⟨zK, hzK⟩ := h.exists_inv hK
    obtain ⟨V, hV⟩ := h.exists_cyc2 hK
    have hzV : zK ∈ V := AscL62.mem_of_index_two (h.isQuatSub hK) hzK hV.le hV.card
    intro x hx
    apply h.typeR.tight K hK zK hzK
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact h.cyc2_comm hJ hK hU hV hx hzV

end SetE

structure Gen (K : Subgroup X) (z : X) (U : Subgroup X) (u b : X) : Prop where
  inv : IsUniqueInvolution K z
  cyc : Cyc2 K U
  zp : Subgroup.zpowers u = U
  b_mem : b ∈ K
  b_not : b ∉ U

namespace Gen

variable {K : Subgroup X} {z : X} {U : Subgroup X} {u b : X}

theorem u_mem (g : Gen K z U u b) : u ∈ U := g.zp ▸ Subgroup.mem_zpowers u

theorem u_mem_K (g : Gen K z U u b) : u ∈ K := g.cyc.le g.u_mem

theorem z_mem_U (g : Gen K z U u b) (hK : IsQuatSub K) : z ∈ U :=
  AscL62.mem_of_index_two hK g.inv g.cyc.le g.cyc.card

theorem mem_zpowers_of_mem_U (g : Gen K z U u b) {x : X} (hx : x ∈ U) :
    ∃ n : ℤ, u ^ n = x := by
  rw [← g.zp] at hx
  exact Subgroup.mem_zpowers_iff.mp hx

theorem b_inv (g : Gen K z U u b) (hK : IsQuatSub K) {c : X} (hc : c ∈ U) :
    b * c * b⁻¹ = c⁻¹ :=
  AscL62.conj_eq_inv_of_not_mem hK g.inv g.cyc.le g.cyc.cyclic g.cyc.card g.b_mem g.b_not hc

theorem orderOf_u (g : Gen K z U u b) : orderOf u = Nat.card ↥U := by
  rw [← Nat.card_zpowers, g.zp]

theorem gen_K [Finite X] (g : Gen K z U u b) {x : X} (hx : x ∈ K) : x ∈ U ∨ b⁻¹ * x ∈ U := by
  by_cases hxU : x ∈ U
  · exact Or.inl hxU
  · exact Or.inr (AscL62.inv_mul_mem_of_index_two g.cyc.le g.cyc.card g.b_mem hx g.b_not hxU)

theorem conj (g : Gen K z U u b) (n : X) :
    Gen (conjSub n K) (n * z * n⁻¹) (conjSub n U) (n * u * n⁻¹) (n * b * n⁻¹) where
  inv := g.inv.conj n
  cyc :=
    ⟨conjSub_mono g.cyc.le, AscL62.isCyclic_conjSub n g.cyc.cyclic, by
      rw [AscL62.natCard_conjSub, AscL62.natCard_conjSub]; exact g.cyc.card⟩
  zp := by
    have := MonoidHom.map_zpowers (MulAut.conj n).toMonoidHom u
    rw [g.zp] at this
    exact this.symm
  b_mem := conj_mem_conjSub g.b_mem
  b_not := fun hb => g.b_not (by
    rw [mem_conjSub_iff] at hb
    simpa [mul_assoc] using hb)

end Gen

namespace SetE

variable (h : SetE r Φ)
include h

theorem exists_gen {K : Subgroup X} (hK : K ∈ Φ) : ∃ z U u b, Gen K z U u b := by
  obtain ⟨z, hz⟩ := h.exists_inv hK
  obtain ⟨U, hU⟩ := h.exists_cyc2 hK
  haveI := hU.cyclic
  obtain ⟨u, hu⟩ := IsCyclic.exists_generator (α := ↥U)
  have hzp : Subgroup.zpowers (u : X) = U := by
    ext x
    constructor
    · intro hx
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact U.zpow_mem u.2 n
    · intro hx
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hu ⟨x, hx⟩)
      refine Subgroup.mem_zpowers_iff.mpr ⟨n, ?_⟩
      simpa using congrArg Subtype.val hn
  have hlt : U < K := lt_of_le_of_ne hU.le (by
    intro e
    have := hU.card
    rw [e] at this
    have hpos : 0 < Nat.card ↥K := Nat.card_pos
    omega)
  obtain ⟨b, hbK, hbU⟩ := SetLike.exists_of_lt hlt
  exact ⟨z, U, u, b, ⟨hz, hU, hzp, hbK, hbU⟩⟩

theorem commutator_mem {K U : Subgroup X} {z : X} {u b : X} (hK : K ∈ Φ) (g : Gen K z U u b)
    {x y : X} (hx : x ∈ Subgroup.normalizer (K : Set X)) (hy : y ∈ K) (hyU : y ∉ U) :
    y⁻¹ * (x * y * x⁻¹) ∈ U := by
  have hxU : x ∈ Subgroup.normalizer (U : Set X) :=
    mem_normalizer_of_mem_USet h.four_le h.typeR.hyp (fun _ hJ => h.isPGroup hJ)
      (fun _ hJ => h.card_eq hJ) hK (h.cyc2_mem_USet hK g.cyc) g.cyc.le hx
  have hxyK : x * y * x⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hx y).mp hy
  have hxyU : x * y * x⁻¹ ∉ U := by
    intro hmem
    apply hyU
    have h1 := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (U : Set X)).inv_mem hxU)
      (x * y * x⁻¹)).mp hmem
    simpa [mul_assoc] using h1
  exact AscL62.inv_mul_mem_of_index_two g.cyc.le g.cyc.card hy hxyK hyU hxyU

theorem commutes_of_le_normalizer {J K : Subgroup X} (hJ : J ∈ Φ) (hK : K ∈ Φ) (hne : J ≠ K)
    (hle : J ≤ Subgroup.normalizer (K : Set X)) : Commutes J K := by
  have hmem : J ∈ omegaNbr Φ K :=
    (TC.mem_omegaNbr_iff h.typeR.hyp (fun _ hJ => h.isPGroup hJ)).mpr ⟨hJ, hne, hle⟩
  have hmem' : K ∈ omegaNbr Φ J := Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen h.typeR.hyp hK hJ hmem
  have hle' : K ≤ Subgroup.normalizer (J : Set X) :=
    ((TC.mem_omegaNbr_iff h.typeR.hyp (fun _ hJ => h.isPGroup hJ)).mp hmem').2.2
  intro x hx y hy
  have h1 : x * y * x⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hle hx) y).mp hy
  have h2 : y * x⁻¹ * y⁻¹ ∈ J :=
    (Subgroup.mem_normalizer_iff.mp (hle' hy) x⁻¹).mp (J.inv_mem hx)
  have hcK : x * y * x⁻¹ * y⁻¹ ∈ K := K.mul_mem h1 (K.inv_mem hy)
  have hcJ : x * y * x⁻¹ * y⁻¹ ∈ J := by
    have := J.mul_mem hx h2
    simpa [mul_assoc] using this
  have hbot : x * y * x⁻¹ * y⁻¹ ∈ J ⊓ K := ⟨hcJ, hcK⟩
  rw [h.inf_eq_bot hJ hK hne, Subgroup.mem_bot] at hbot
  calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
    _ = y * x := by rw [hbot, one_mul]

theorem omegaNbr_iff {J K : Subgroup X} (hK : K ∈ Φ) :
    J ∈ omegaNbr Φ K ↔ J ∈ Φ ∧ J ≠ K ∧ Commutes J K := by
  rw [TC.mem_omegaNbr_iff h.typeR.hyp (fun _ hJ => h.isPGroup hJ)]
  constructor
  · rintro ⟨hJ, hne, hle⟩
    exact ⟨hJ, hne, h.commutes_of_le_normalizer hJ hK hne hle⟩
  · rintro ⟨hJ, hne, hc⟩
    exact ⟨hJ, hne, AscL62.le_normalizer_of_commutes hc⟩

theorem refl_coeff {J K : Subgroup X} {zJ zK : X} {UJ UK : Subgroup X} {uJ uK bJ bK : X}
    (hJ : J ∈ Φ) (hK : K ∈ Φ) (gJ : Gen J zJ UJ uJ bJ) (gK : Gen K zK UK uK bK) :
    ∃ c : ℤ, bK * uJ * bK⁻¹ = uJ * uK ^ c := by
  have hbK : bK⁻¹ ∈ K := K.inv_mem gK.b_mem
  have hbU : bK⁻¹ ∉ UK := fun hm => gK.b_not (by simpa using UK.inv_mem hm)
  have hcm := h.commutator_mem hK gK (h.cyc2_le_normalizer hJ hK gJ.cyc gJ.u_mem) hbK hbU
  rw [inv_inv] at hcm
  obtain ⟨c, hc⟩ := gK.mem_zpowers_of_mem_U hcm
  refine ⟨c, ?_⟩
  have hcomm : uK ^ c * uJ = uJ * uK ^ c :=
    h.cyc2_comm hK hJ gK.cyc gJ.cyc (UK.zpow_mem gK.u_mem c) gJ.u_mem
  calc bK * uJ * bK⁻¹ = (bK * (uJ * bK⁻¹ * uJ⁻¹)) * uJ := by group
    _ = uK ^ c * uJ := by rw [hc]
    _ = uJ * uK ^ c := hcomm

theorem refl_z_nc {J K : Subgroup X} {zJ zK : X} {UJ UK : Subgroup X} {uJ uK bJ bK : X}
    (hJ : J ∈ Φ) (hK : K ∈ Φ) (gJ : Gen J zJ UJ uJ bJ) (gK : Gen K zK UK uK bK)
    (hne : J ≠ K) (hnc : ¬ Commutes J K) : bJ * zK * bJ⁻¹ = zK * zJ := by
  have hqJ := h.isQuatSub hJ
  have hqK := h.isQuatSub hK
  have hzKU : zK ∈ UK := gK.z_mem_U hqK
  have hzJU : zJ ∈ UJ := gJ.z_mem_U hqJ
  have hzKN : zK ∈ Subgroup.normalizer (J : Set X) := h.normalizes hJ hK gK.inv
  have hbJ : bJ⁻¹ ∈ J := J.inv_mem gJ.b_mem
  have hbU : bJ⁻¹ ∉ UJ := fun hm => gJ.b_not (by simpa using UJ.inv_mem hm)
  have hcm := h.commutator_mem hJ gJ hzKN hbJ hbU
  rw [inv_inv, inv_eq_of_mul_eq_one_right gK.inv.sq] at hcm
  set d : X := bJ * (zK * bJ⁻¹ * zK) with hd
  set e : X := bJ * zK * bJ⁻¹ with he
  have hde : d = e * zK := by simp only [hd, he]; group
  have hee : e * e = 1 := by
    calc e * e = bJ * (zK * zK) * bJ⁻¹ := by simp only [he]; group
      _ = 1 := by rw [gK.inv.sq]; group
  have hcomm : d * zK = zK * d := h.cyc2_comm hJ hK gJ.cyc gK.cyc hcm hzKU
  have hze : e = zK * e * zK := by
    calc e = e * (zK * zK) := by rw [gK.inv.sq, mul_one]
      _ = (e * zK) * zK := by group
      _ = zK * (e * zK) := by rw [← hde]; exact hcomm
      _ = zK * e * zK := by group
  have hdd : d * d = 1 := by
    calc d * d = e * (zK * e * zK) := by rw [hde]; group
      _ = e * e := by rw [← hze]
      _ = 1 := hee
  rcases gJ.inv.unique d (gJ.cyc.le hcm) hdd with hd1 | hdz
  ·
    exfalso
    apply hnc
    have hez : e = zK := by
      have h1 : e * zK = 1 := by rw [← hde]; exact hd1
      calc e = e * zK * zK⁻¹ := by group
        _ = zK⁻¹ := by rw [h1, one_mul]
        _ = zK := inv_eq_of_mul_eq_one_right gK.inv.sq
    have hbz : bJ * zK = zK * bJ := by
      have : bJ * zK * bJ⁻¹ = zK := hez
      calc bJ * zK = bJ * zK * bJ⁻¹ * bJ := by group
        _ = zK * bJ := by rw [this]
    have hJC : J ≤ Subgroup.centralizer ({zK} : Set X) := by
      intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      rcases gJ.gen_K hx with hxU | hxw
      · exact h.cyc2_comm hJ hK gJ.cyc gK.cyc hxU hzKU
      · have hw : x = bJ * (bJ⁻¹ * x) := by group
        have hwz : (bJ⁻¹ * x) * zK = zK * (bJ⁻¹ * x) :=
          h.cyc2_comm hJ hK gJ.cyc gK.cyc hxw hzKU
        rw [hw]
        calc bJ * (bJ⁻¹ * x) * zK = bJ * ((bJ⁻¹ * x) * zK) := by group
          _ = bJ * (zK * (bJ⁻¹ * x)) := by rw [hwz]
          _ = (bJ * zK) * (bJ⁻¹ * x) := by group
          _ = (zK * bJ) * (bJ⁻¹ * x) := by rw [hbz]
          _ = zK * (bJ * (bJ⁻¹ * x)) := by group
    exact h.commutes_of_le_normalizer hJ hK hne
      (hJC.trans (h.typeR.tight K hK zK gK.inv))
  ·
    have hzz : zJ * zK = zK * zJ := h.cyc2_comm hJ hK gJ.cyc gK.cyc hzJU hzKU
    have h1 : e = zJ * zK := by
      calc e = e * zK * zK := by
            calc e = e * (zK * zK) := by rw [gK.inv.sq, mul_one]
              _ = e * zK * zK := by group
        _ = d * zK := by rw [hde]
        _ = zJ * zK := by rw [hdz]
    exact h1.trans hzz

theorem card_U {K U : Subgroup X} {z : X} {u b : X} (hK : K ∈ Φ) (g : Gen K z U u b) :
    Nat.card ↥U = 2 ^ (r - 1) := by
  have h1 := g.cyc.card
  rw [h.card_eq hK] at h1
  obtain ⟨k, hk⟩ : ∃ k, r = k + 1 := ⟨r - 1, by have := h.four_le; omega⟩
  rw [hk, pow_succ] at h1
  rw [hk, Nat.add_sub_cancel]
  omega

theorem orderOf_u {K U : Subgroup X} {z : X} {u b : X} (hK : K ∈ Φ) (g : Gen K z U u b) :
    orderOf u = 2 ^ (r - 1) := by
  rw [g.orderOf_u, h.card_U hK g]

theorem u_pow_half {K U : Subgroup X} {z : X} {u b : X} (hK : K ∈ Φ) (g : Gen K z U u b) :
    u ^ (2 ^ (r - 2)) = z := by
  have hr := h.four_le
  have hdvd : 2 ^ (r - 2) ∣ orderOf u := by
    rw [h.orderOf_u hK g]
    exact pow_dvd_pow 2 (by omega)
  have hord : orderOf (u ^ (2 ^ (r - 2))) = 2 := by
    rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) hdvd, h.orderOf_u hK g]
    obtain ⟨k, hk⟩ : ∃ k, r = k + 2 := ⟨r - 2, by omega⟩
    rw [hk, Nat.add_sub_cancel, show k + 2 - 1 = k + 1 by omega, pow_succ]
    exact Nat.mul_div_cancel_left 2 (pow_pos two_pos k)
  have hsq : u ^ (2 ^ (r - 2)) * u ^ (2 ^ (r - 2)) = 1 := by
    have := pow_orderOf_eq_one (u ^ (2 ^ (r - 2)))
    rwa [hord, pow_two] at this
  have hne : u ^ (2 ^ (r - 2)) ≠ 1 := by
    intro e
    rw [e, orderOf_one] at hord
    omega
  exact (g.inv.unique _ (K.pow_mem g.u_mem_K _) hsq).resolve_left hne

theorem odd_coeff {J K : Subgroup X} {zJ zK : X} {UJ UK : Subgroup X} {uJ uK bJ bK : X}
    (hJ : J ∈ Φ) (hK : K ∈ Φ) (gJ : Gen J zJ UJ uJ bJ) (gK : Gen K zK UK uK bK)
    (hne : K ≠ J) (hnc : ¬ Commutes K J) {c : ℤ} (hc : bK * uJ * bK⁻¹ = uJ * uK ^ c) :
    Odd c := by
  have hline : bK * zJ * bK⁻¹ = zJ * zK := h.refl_z_nc hK hJ gK gJ hne hnc
  have hcomm : Commute uJ (uK ^ c) :=
    (h.cyc2_comm hJ hK gJ.cyc gK.cyc gJ.u_mem (UK.zpow_mem gK.u_mem c))
  have h1 : (bK * uJ * bK⁻¹) ^ (2 ^ (r - 2)) = zJ * zK := by
    rw [conj_pow, h.u_pow_half hJ gJ, hline]
  rw [hc, hcomm.mul_pow, h.u_pow_half hJ gJ] at h1
  have h2 : (uK ^ c) ^ (2 ^ (r - 2)) = zK ^ c := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h.u_pow_half hK gK]
  rw [h2] at h1
  have h3 : zK ^ c = zK := mul_left_cancel h1
  by_contra hodd
  rw [Int.not_odd_iff_even] at hodd
  obtain ⟨k, hk⟩ := hodd
  have : zK ^ c = 1 := by
    rw [hk, ← two_mul, zpow_mul, zpow_two, gK.inv.sq, one_zpow]
  exact gK.inv.ne_one (h3.symm.trans this)

theorem gen_zpow {K : Subgroup X} {z z' : X} {U U' : Subgroup X} {u b u' b' : X} (hK : K ∈ Φ)
    (g : Gen K z U u b) (g' : Gen K z' U' u' b') : ∃ w : ℤ, Odd w ∧ u ^ w = u' := by
  have hUU : U = U' := h.cyc2_eq hK g.cyc g'.cyc
  subst hUU
  obtain ⟨w, hw⟩ := g.mem_zpowers_of_mem_U g'.u_mem
  refine ⟨w, ?_, hw⟩
  by_contra hodd
  rw [Int.not_odd_iff_even] at hodd
  obtain ⟨k, hk⟩ := hodd
  have hr := h.four_le
  have hpow1 : u ^ (2 ^ (r - 1)) = 1 := by
    have := pow_orderOf_eq_one u
    rwa [h.orderOf_u hK g] at this
  have e : (w * ((2 ^ (r - 2) : ℕ) : ℤ)) = ((2 ^ (r - 1) : ℕ) : ℤ) * k := by
    rw [hk]
    push_cast
    have : (2 : ℤ) ^ (r - 1) = 2 * 2 ^ (r - 2) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [this]
    ring
  have h1 : u' ^ (2 ^ (r - 2)) = 1 := by
    rw [← hw, ← zpow_natCast, ← zpow_mul, e, zpow_mul, zpow_natCast, hpow1, one_zpow]
  exact g'.inv.ne_one ((h.u_pow_half hK g').symm.trans h1)

theorem conj_gen_coeff {P Q T : Subgroup X} {zP zQ zT : X} {UP UQ UT : Subgroup X}
    {uP uQ uT bP bQ bT : X} (hP : P ∈ Φ) (hQ : Q ∈ Φ) (hT : T ∈ Φ) (gP : Gen P zP UP uP bP)
    (gQ : Gen Q zQ UQ uQ bQ) (gT : Gen T zT UT uT bT) {c₁ c₂ c₃ : ℤ}
    (e₁ : bQ * uP * bQ⁻¹ = uP * uQ ^ c₁) (e₂ : bT * uP * bT⁻¹ = uP * uT ^ c₂)
    (e₃ : bT * uQ * bT⁻¹ = uQ * uT ^ c₃) :
    bT * (bQ * uP * bQ⁻¹) * bT⁻¹ = (bQ * uP * bQ⁻¹) * uT ^ (c₂ + c₁ * c₃) := by
  have hQT : uQ * uT ^ c₃ = uT ^ c₃ * uQ :=
    h.cyc2_comm hQ hT gQ.cyc gT.cyc gQ.u_mem (UT.zpow_mem gT.u_mem c₃)
  have hTQ : uT ^ c₂ * uQ ^ c₁ = uQ ^ c₁ * uT ^ c₂ :=
    h.cyc2_comm hT hQ gT.cyc gQ.cyc (UT.zpow_mem gT.u_mem c₂) (UQ.zpow_mem gQ.u_mem c₁)
  rw [e₁]
  have e4 : bT * (uP * uQ ^ c₁) * bT⁻¹ = (bT * uP * bT⁻¹) * (bT * uQ * bT⁻¹) ^ c₁ := by
    rw [conj_zpow]
    group
  rw [e4, e₂, e₃, (show Commute uQ (uT ^ c₃) from hQT).mul_zpow, ← zpow_mul]
  calc uP * uT ^ c₂ * (uQ ^ c₁ * uT ^ (c₃ * c₁))
      = uP * (uT ^ c₂ * uQ ^ c₁) * uT ^ (c₃ * c₁) := by group
    _ = uP * (uQ ^ c₁ * uT ^ c₂) * uT ^ (c₃ * c₁) := by rw [hTQ]
    _ = uP * uQ ^ c₁ * (uT ^ c₂ * uT ^ (c₃ * c₁)) := by group
    _ = uP * uQ ^ c₁ * uT ^ (c₂ + c₁ * c₃) := by rw [← zpow_add, mul_comm c₃ c₁]

theorem four_dvd_pow : (4 : ℤ) ∣ ((2 ^ (r - 1) : ℕ) : ℤ) := by
  have hr := h.four_le
  have : (2 : ℕ) ^ 2 ∣ 2 ^ (r - 1) := pow_dvd_pow 2 (by omega)
  exact_mod_cast this

theorem sign_aux {P Q T : Subgroup X} {zP zQ zT : X} {UP UQ UT : Subgroup X}
    {uP uQ uT bP bQ bT : X} (hP : P ∈ Φ) (hQ : Q ∈ Φ) (hT : T ∈ Φ) (gP : Gen P zP UP uP bP)
    (gQ : Gen Q zQ UQ uQ bQ) (gT : Gen T zT UT uT bT) (hPQ : NC P Q) (hPT : NC P T)
    (hQT : NC Q T) {c₁ c₂ c₃ : ℤ} (e₁ : bQ * uP * bQ⁻¹ = uP * uQ ^ c₁)
    (e₂ : bT * uP * bT⁻¹ = uP * uT ^ c₂) (e₃ : bT * uQ * bT⁻¹ = uQ * uT ^ c₃) :
    Odd c₁ ∧ Odd c₂ ∧ Odd c₃ ∧
      ((T = conjSub bQ P → (c₂ + c₁ * c₃) % 4 = 2) ∧
        (T ≠ conjSub bQ P → (c₂ + c₁ * c₃) % 4 = 0)) := by
  have o₁ : Odd c₁ := h.odd_coeff hP hQ gP gQ hPQ.1.symm (fun hc => hPQ.2 hc.symm) e₁
  have o₂ : Odd c₂ := h.odd_coeff hP hT gP gT hPT.1.symm (fun hc => hPT.2 hc.symm) e₂
  have o₃ : Odd c₃ := h.odd_coeff hQ hT gQ gT hQT.1.symm (fun hc => hQT.2 hc.symm) e₃
  refine ⟨o₁, o₂, o₃, ?_⟩
  have hSΦ : conjSub bQ P ∈ Φ := h.typeR.hyp.conjInvariant bQ P hP
  have gS := gP.conj bQ
  have hbT := h.conj_gen_coeff hP hQ hT gP gQ gT e₁ e₂ e₃
  have heven : Even (c₂ + c₁ * c₃) := o₂.add_odd (o₁.mul o₃)
  have h4 := h.four_dvd_pow
  have hordT : orderOf uT = 2 ^ (r - 1) := h.orderOf_u hT gT
  have hdvd1 : ∀ e : ℤ, uT ^ e = 1 → (4 : ℤ) ∣ e := by
    intro e he
    have := orderOf_dvd_iff_zpow_eq_one.mpr he
    rw [hordT] at this
    exact h4.trans this
  constructor
  · intro hTS
    have gT' : Gen (conjSub bQ P) zT UT uT bT := hTS ▸ gT
    have hUU : UT = conjSub bQ UP := h.cyc2_eq hSΦ gT'.cyc gS.cyc
    have hcU : bQ * uP * bQ⁻¹ ∈ UT := hUU ▸ gS.u_mem
    have hinv : bT * (bQ * uP * bQ⁻¹) * bT⁻¹ = (bQ * uP * bQ⁻¹)⁻¹ :=
      gT'.b_inv (h.isQuatSub hSΦ) hcU
    obtain ⟨w, hw, hwu⟩ := h.gen_zpow hSΦ gT' gS
    set u' := bQ * uP * bQ⁻¹ with hu'
    set e := c₂ + c₁ * c₃ with he
    have h1 : uT ^ e = u'⁻¹ * u'⁻¹ := by
      have : u'⁻¹ = u' * uT ^ e := hinv.symm.trans hbT
      calc uT ^ e = u'⁻¹ * (u' * uT ^ e) := by group
        _ = u'⁻¹ * u'⁻¹ := by rw [← this]
    have h2 : uT ^ (e + w + w) = 1 := by
      calc uT ^ (e + w + w) = uT ^ e * uT ^ w * uT ^ w := by rw [zpow_add, zpow_add]
        _ = u'⁻¹ * u'⁻¹ * u' * u' := by rw [h1, hwu]
        _ = 1 := by group
    have h3 := hdvd1 _ h2
    rw [Int.odd_iff] at hw
    omega
  · intro hTS
    by_cases hc : Commutes T (conjSub bQ P)
    · have h1 : bT * (bQ * uP * bQ⁻¹) = (bQ * uP * bQ⁻¹) * bT := hc bT gT.b_mem _ gS.u_mem_K
      have h2 : uT ^ (c₂ + c₁ * c₃) = 1 := by
        have : bT * (bQ * uP * bQ⁻¹) * bT⁻¹ = bQ * uP * bQ⁻¹ := by
          rw [h1]; group
        rw [this] at hbT
        exact (mul_eq_left.mp hbT.symm)
      exact Int.emod_eq_zero_of_dvd (hdvd1 _ h2)
    · exfalso
      have hline : bT * (bQ * zP * bQ⁻¹) * bT⁻¹ = (bQ * zP * bQ⁻¹) * zT :=
        h.refl_z_nc hT hSΦ gT gS hTS hc
      have hpow : (bQ * uP * bQ⁻¹) ^ (2 ^ (r - 2)) = bQ * zP * bQ⁻¹ := h.u_pow_half hSΦ gS
      have h1 : (bT * (bQ * uP * bQ⁻¹) * bT⁻¹) ^ (2 ^ (r - 2)) =
          (bQ * zP * bQ⁻¹) * zT := by
        rw [conj_pow, hpow, hline]
      rw [hbT] at h1
      have hcomm : Commute (bQ * uP * bQ⁻¹) (uT ^ (c₂ + c₁ * c₃)) := by
        rw [e₁]
        exact Commute.mul_left
          (h.cyc2_comm hP hT gP.cyc gT.cyc gP.u_mem (UT.zpow_mem gT.u_mem _))
          (h.cyc2_comm hQ hT gQ.cyc gT.cyc (UQ.zpow_mem gQ.u_mem c₁)
            (UT.zpow_mem gT.u_mem _))
      rw [hcomm.mul_pow, hpow] at h1
      have h2 : (uT ^ (c₂ + c₁ * c₃)) ^ (2 ^ (r - 2)) = 1 := by
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h.u_pow_half hT gT]
        obtain ⟨k, hk⟩ := heven
        rw [hk, ← two_mul, zpow_mul, zpow_two, gT.inv.sq, one_zpow]
      rw [h2, mul_one] at h1
      exact gT.inv.ne_one (mul_eq_left.mp h1.symm)

theorem refl_z_of_not_nc {J K : Subgroup X} {zJ zK : X} {UJ UK : Subgroup X}
    {uJ uK bJ bK : X} (gJ : Gen J zJ UJ uJ bJ) (gK : Gen K zK UK uK bK) (hnc : ¬ NC J K) :
    bJ * zK * bJ⁻¹ = zK := by
  by_cases hJK : J = K
  · subst hJK
    have := AscL62.uniqueInvolution_comm gK.inv gJ.b_mem
    calc bJ * zK * bJ⁻¹ = zK * bJ * bJ⁻¹ := by rw [this]
      _ = zK := by group
  · have hc : Commutes J K := by
      by_contra hc'
      exact hnc ⟨hJK, hc'⟩
    have := hc bJ gJ.b_mem zK gK.inv.mem
    calc bJ * zK * bJ⁻¹ = zK * bJ * bJ⁻¹ := by rw [this]
      _ = zK := by group

end SetE

@[expose] def ell (c : ℤ) : ZMod 2 := if c % 4 = 3 then 1 else 0

theorem sign_arith {c₁ c₂ c₃ : ℤ} (h1 : Odd c₁) (h2 : Odd c₂) (h3 : Odd c₃) :
    ((c₂ + c₁ * c₃) % 4 = 2 → ell c₂ + ell c₁ + ell c₃ = 0) ∧
      ((c₂ + c₁ * c₃) % 4 = 0 → ell c₂ + ell c₁ + ell c₃ = 1) := by
  rw [Int.odd_iff] at h1 h2 h3
  have hm : (c₂ + c₁ * c₃) % 4 = (c₂ % 4 + c₁ % 4 * (c₃ % 4)) % 4 := by
    simp [Int.add_emod, Int.mul_emod]
  rcases (show c₁ % 4 = 1 ∨ c₁ % 4 = 3 by omega) with a | a <;>
  rcases (show c₂ % 4 = 1 ∨ c₂ % 4 = 3 by omega) with b | b <;>
  rcases (show c₃ % 4 = 1 ∨ c₃ % 4 = 3 by omega) with c | c <;>
  simp [ell, hm, a, b, c] <;> decide

structure GData (K : Subgroup X) where
  z : X
  U : Subgroup X
  u : X
  b : X
  spec : Gen K z U u b

open Classical in
@[expose] noncomputable def nnv {Φ : Set (Subgroup X)} (i j : ↥Φ) : ZMod 2 :=
  if NC i.1 j.1 then 1 else 0

theorem nnv_eq_one_iff {Φ : Set (Subgroup X)} {i j : ↥Φ} : nnv i j = 1 ↔ NC i.1 j.1 := by
  unfold nnv
  split_ifs with hc <;> simp [hc]

theorem nnv_eq_zero_iff {Φ : Set (Subgroup X)} {i j : ↥Φ} : nnv i j = 0 ↔ ¬ NC i.1 j.1 := by
  unfold nnv
  split_ifs with hc <;> simp [hc]

theorem nnv_symm {Φ : Set (Subgroup X)} (i j : ↥Φ) : nnv i j = nnv j i := by
  by_cases hc : NC i.1 j.1
  · rw [nnv_eq_one_iff.mpr hc, nnv_eq_one_iff.mpr hc.symm]
  · rw [nnv_eq_zero_iff.mpr hc, nnv_eq_zero_iff.mpr fun h' => hc h'.symm]

theorem nnv_self {Φ : Set (Subgroup X)} (i : ↥Φ) : nnv i i = 0 :=
  nnv_eq_zero_iff.mpr fun hc => hc.1 rfl

namespace SetE

theorem nonempty_gdata (h : SetE r Φ) {K : Subgroup X} (hK : K ∈ Φ) : Nonempty (GData K) := by
  obtain ⟨z, U, u, b, g⟩ := h.exists_gen hK
  exact ⟨⟨z, U, u, b, g⟩⟩

noncomputable def gd (h : SetE r Φ) (i : ↥Φ) : GData i.1 :=
  Classical.choice (h.nonempty_gdata i.2)

noncomputable def zi (h : SetE r Φ) (i : ↥Φ) : X := (h.gd i).z

noncomputable def Ui (h : SetE r Φ) (i : ↥Φ) : Subgroup X := (h.gd i).U

noncomputable def ui (h : SetE r Φ) (i : ↥Φ) : X := (h.gd i).u

noncomputable def bi (h : SetE r Φ) (i : ↥Φ) : X := (h.gd i).b

theorem gen_spec (h : SetE r Φ) (i : ↥Φ) :
    Gen i.1 (h.zi i) (h.Ui i) (h.ui i) (h.bi i) := (h.gd i).spec

theorem zi_comm (h : SetE r Φ) (i j : ↥Φ) : h.zi i * h.zi j = h.zi j * h.zi i :=
  h.cyc2_comm i.2 j.2 (h.gen_spec i).cyc (h.gen_spec j).cyc
    ((h.gen_spec i).z_mem_U (h.isQuatSub i.2)) ((h.gen_spec j).z_mem_U (h.isQuatSub j.2))

theorem zi_inj (h : SetE r Φ) {i j : ↥Φ} (e : h.zi i = h.zi j) : i = j := by
  by_contra hne
  exact h.inv_ne i.2 j.2 (fun e' => hne (Subtype.ext e')) (h.gen_spec i).inv
    (h.gen_spec j).inv e

theorem refl_nn_pow (h : SetE r Φ) (i j : ↥Φ) :
    h.bi i * h.zi j * (h.bi i)⁻¹ = h.zi j * h.zi i ^ (nnv i j).val := by
  by_cases hc : NC i.1 j.1
  · have h1 : nnv i j = 1 := nnv_eq_one_iff.mpr hc
    rw [h1, ZMod.val_one, pow_one]
    exact h.refl_z_nc i.2 j.2 (h.gen_spec i) (h.gen_spec j) hc.1 hc.2
  · have h0 : nnv i j = 0 := nnv_eq_zero_iff.mpr hc
    rw [h0, ZMod.val_zero, pow_zero, mul_one]
    exact h.refl_z_of_not_nc (h.gen_spec i) (h.gen_spec j) hc

noncomputable def coeff (h : SetE r Φ) (i j : ↥Φ) : ℤ :=
  Classical.choose (h.refl_coeff i.2 j.2 (h.gen_spec i) (h.gen_spec j))

theorem coeff_spec (h : SetE r Φ) (i j : ↥Φ) :
    h.bi j * h.ui i * (h.bi j)⁻¹ = h.ui i * h.ui j ^ h.coeff i j :=
  Classical.choose_spec (h.refl_coeff i.2 j.2 (h.gen_spec i) (h.gen_spec j))

theorem nnv_add (h : SetE r Φ) (t p q s : ↥Φ) (hs : h.zi s = h.zi p * h.zi q) :
    nnv t s = nnv t p + nnv t q := by
  have e1 := h.refl_nn_pow t p
  have e2 := h.refl_nn_pow t q
  have e3 := h.refl_nn_pow t s
  set w := h.zi t with hw
  have hw1 : w ≠ 1 := (h.gen_spec t).inv.ne_one
  have hw2 : orderOf w = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact (h.gen_spec t).inv.sq) hw1
  have hconj : h.bi t * h.zi s * (h.bi t)⁻¹ =
      (h.bi t * h.zi p * (h.bi t)⁻¹) * (h.bi t * h.zi q * (h.bi t)⁻¹) := by
    rw [hs]
    group
  rw [e3, e1, e2, hs] at hconj
  have hcq : w ^ (nnv t p).val * h.zi q = h.zi q * w ^ (nnv t p).val :=
    (Commute.pow_left (show Commute w (h.zi q) from h.zi_comm t q) _).eq
  have h4 : h.zi p * h.zi q * w ^ (nnv t s).val =
      h.zi p * h.zi q * (w ^ (nnv t p).val * w ^ (nnv t q).val) := by
    calc h.zi p * h.zi q * w ^ (nnv t s).val
        = h.zi p * w ^ (nnv t p).val * (h.zi q * w ^ (nnv t q).val) := hconj
      _ = h.zi p * (w ^ (nnv t p).val * h.zi q) * w ^ (nnv t q).val := by group
      _ = h.zi p * (h.zi q * w ^ (nnv t p).val) * w ^ (nnv t q).val := by rw [hcq]
      _ = h.zi p * h.zi q * (w ^ (nnv t p).val * w ^ (nnv t q).val) := by group
  have h5 := mul_left_cancel h4
  rw [← pow_add, pow_eq_pow_iff_modEq, hw2] at h5
  have h6 := (ZMod.natCast_eq_natCast_iff _ _ _).mpr h5
  simpa using h6

theorem conj_mem (h : SetE r Φ) (p q : ↥Φ) : conjSub (h.bi q) p.1 ∈ Φ :=
  h.typeR.hyp.conjInvariant (h.bi q) p.1 p.2

theorem zi_conj (h : SetE r Φ) (p q : ↥Φ) (hnc : NC p.1 q.1) :
    h.zi ⟨conjSub (h.bi q) p.1, h.conj_mem p q⟩ = h.zi p * h.zi q := by
  have h1 : h.zi ⟨conjSub (h.bi q) p.1, h.conj_mem p q⟩ = h.bi q * h.zi p * (h.bi q)⁻¹ :=
    (h.gen_spec ⟨_, h.conj_mem p q⟩).inv.eq ((h.gen_spec p).inv.conj (h.bi q))
  rw [h1, h.refl_nn_pow q p, nnv_eq_one_iff.mpr hnc.symm, ZMod.val_one, pow_one]

theorem zSub_comm (h : SetE r Φ) : (Set.range h.zi).Pairwise Commute := by
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _
  exact h.zi_comm i j

noncomputable abbrev zSub (h : SetE r Φ) : Subgroup X :=
  Subgroup.closure (Set.range h.zi)

noncomputable instance instCommGroupZSub (h : SetE r Φ) : CommGroup ↥h.zSub :=
  Subgroup.closureCommGroupOfComm h.zSub_comm

theorem mem_zSub (h : SetE r Φ) (i : ↥Φ) : h.zi i ∈ h.zSub := Subgroup.subset_closure ⟨i, rfl⟩

@[expose] noncomputable def octa (h : SetE r Φ) : OctaSys ↥Φ ↥h.zSub where
  z i := ⟨h.zi i, h.mem_zSub i⟩
  nn := nnv
  sg i j := ell (h.coeff i j)
  sq := by
    rintro ⟨v, hv⟩
    apply Subtype.ext
    show v * v = 1
    induction hv using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact (h.gen_spec i).inv.sq
    | one => simp
    | mul x y hx hy ihx ihy =>
      have hc : x * y = y * x :=
        congrArg Subtype.val (mul_comm (⟨x, hx⟩ : ↥h.zSub) ⟨y, hy⟩)
      calc x * y * (x * y) = x * (y * x) * y := by group
        _ = x * (x * y) * y := by rw [hc]
        _ = (x * x) * (y * y) := by group
        _ = 1 := by rw [ihx, ihy, one_mul]
    | inv x hx ihx =>
      rw [← mul_inv_rev, ihx, inv_one]
  z_inj := fun {i j} e => h.zi_inj (congrArg Subtype.val e)
  z_ne := fun i e => (h.gen_spec i).inv.ne_one (congrArg Subtype.val e)
  nn_self := nnv_self
  nn_symm := nnv_symm
  nn_add := fun t p q s hs => h.nnv_add t p q s (congrArg Subtype.val hs)
  third := by
    intro p q hpq
    refine ⟨⟨conjSub (h.bi q) p.1, h.conj_mem p q⟩, ?_⟩
    apply Subtype.ext
    exact h.zi_conj p q (nnv_eq_one_iff.mp hpq)
  sign_col := by
    intro p q t hpq hpt hqt hz
    have hPQ := nnv_eq_one_iff.mp hpq
    have hPT := nnv_eq_one_iff.mp hpt
    have hQT := nnv_eq_one_iff.mp hqt
    obtain ⟨o1, o2, o3, hmod, -⟩ := h.sign_aux p.2 q.2 t.2 (h.gen_spec p) (h.gen_spec q)
      (h.gen_spec t) hPQ hPT hQT (h.coeff_spec p q) (h.coeff_spec p t) (h.coeff_spec q t)
    have hTS : t.1 = conjSub (h.bi q) p.1 := by
      have e1 : h.zi t = h.zi ⟨conjSub (h.bi q) p.1, h.conj_mem p q⟩ := by
        rw [h.zi_conj p q hPQ]
        exact congrArg Subtype.val hz
      exact congrArg Subtype.val (h.zi_inj e1)
    exact (sign_arith o1 o2 o3).1 (hmod hTS)
  sign_ncol := by
    intro p q t hpq hpt hqt hz
    have hPQ := nnv_eq_one_iff.mp hpq
    have hPT := nnv_eq_one_iff.mp hpt
    have hQT := nnv_eq_one_iff.mp hqt
    obtain ⟨o1, o2, o3, -, hmod⟩ := h.sign_aux p.2 q.2 t.2 (h.gen_spec p) (h.gen_spec q)
      (h.gen_spec t) hPQ hPT hQT (h.coeff_spec p q) (h.coeff_spec p t) (h.coeff_spec q t)
    have hTS : t.1 ≠ conjSub (h.bi q) p.1 := by
      intro e
      apply hz
      have e1 : t = ⟨conjSub (h.bi q) p.1, h.conj_mem p q⟩ := Subtype.ext e
      apply Subtype.ext
      show h.zi t = h.zi p * h.zi q
      rw [e1]
      exact h.zi_conj p q hPQ
    exact (sign_arith o1 o2 o3).2 (hmod hTS)

section Aux

variable (h : SetE r Φ)
include h

theorem refl_mul_eq (t p₀ p₁ : ↥Φ) (hn : nnv t p₀ = nnv t p₁) :
    h.bi t * (h.zi p₀ * h.zi p₁) * (h.bi t)⁻¹ = h.zi p₀ * h.zi p₁ := by
  have e0 := h.refl_nn_pow t p₀
  have e1 := h.refl_nn_pow t p₁
  have e2 : h.bi t * (h.zi p₀ * h.zi p₁) * (h.bi t)⁻¹ =
      (h.bi t * h.zi p₀ * (h.bi t)⁻¹) * (h.bi t * h.zi p₁ * (h.bi t)⁻¹) := by group
  rw [e2, e0, e1, hn]
  have hw2 : h.zi t * h.zi t = 1 := (h.gen_spec t).inv.sq
  have hcomm : h.zi t ^ (nnv t p₁).val * h.zi p₁ = h.zi p₁ * h.zi t ^ (nnv t p₁).val :=
    (Commute.pow_left (show Commute (h.zi t) (h.zi p₁) from h.zi_comm t p₁) _).eq
  calc h.zi p₀ * h.zi t ^ (nnv t p₁).val * (h.zi p₁ * h.zi t ^ (nnv t p₁).val)
      = h.zi p₀ * (h.zi t ^ (nnv t p₁).val * h.zi p₁) * h.zi t ^ (nnv t p₁).val := by group
    _ = h.zi p₀ * (h.zi p₁ * h.zi t ^ (nnv t p₁).val) * h.zi t ^ (nnv t p₁).val := by
        rw [hcomm]
    _ = h.zi p₀ * h.zi p₁ * (h.zi t ^ (nnv t p₁).val * h.zi t ^ (nnv t p₁).val) := by group
    _ = h.zi p₀ * h.zi p₁ := by
        rw [← pow_add, ← two_mul, pow_mul, pow_two, hw2, one_pow, mul_one]

theorem inv_eq_zi {K : Subgroup X} (hK : K ∈ Φ) {u : X} (hu : IsUniqueInvolution K u) :
    u = h.zi ⟨K, hK⟩ :=
  hu.eq (h.gen_spec ⟨K, hK⟩).inv

theorem le_centralizer_of_not_nc {i j : ↥Φ} (hnc : ¬ NC i.1 j.1) :
    j.1 ≤ Subgroup.centralizer ({h.zi i} : Set X) := by
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  by_cases hij : i.1 = j.1
  · have hx' : x ∈ i.1 := hij ▸ hx
    exact AscL62.uniqueInvolution_comm (h.gen_spec i).inv hx'
  · have hc : Commutes i.1 j.1 := by
      by_contra hc'
      exact hnc ⟨hij, hc'⟩
    exact (hc _ (h.gen_spec i).inv.mem x hx).symm

theorem le_centralizer_sup (p₀ p₁ t : ↥Φ) (hn : nnv t p₀ = nnv t p₁) :
    t.1 ≤ Subgroup.centralizer ({h.zi p₀} : Set X) ⊔
      Subgroup.centralizer ({h.zi p₀ * h.zi p₁} : Set X) := by
  intro x hx
  have hU : ∀ {y : X}, y ∈ h.Ui t → y ∈ Subgroup.centralizer ({h.zi p₀} : Set X) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact h.cyc2_comm t.2 p₀.2 (h.gen_spec t).cyc (h.gen_spec p₀).cyc hy
      ((h.gen_spec p₀).z_mem_U (h.isQuatSub p₀.2))
  rcases (h.gen_spec t).gen_K hx with hxU | hw
  · exact Subgroup.mem_sup_left (hU hxU)
  · have hb : h.bi t ∈ Subgroup.centralizer ({h.zi p₀ * h.zi p₁} : Set X) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have := h.refl_mul_eq t p₀ p₁ hn
      calc h.bi t * (h.zi p₀ * h.zi p₁) = h.bi t * (h.zi p₀ * h.zi p₁) * (h.bi t)⁻¹ * h.bi t := by
            group
        _ = (h.zi p₀ * h.zi p₁) * h.bi t := by rw [this]
    have hx' : x = h.bi t * ((h.bi t)⁻¹ * x) := by group
    rw [hx']
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hb) (Subgroup.mem_sup_left (hU hw))

end Aux

end SetE

end SetE

end CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes
