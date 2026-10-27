module

public import CFSG.GH74.Generic.BProg.B2.Defs
public import CFSG.Foundations.HigherElementaryThompson
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.GH74.Generic.BProg.B2.T4

open CFSG CFSG.GH74.GLS CFSG.ABGLocalTools Subgroup

namespace T4Basic

variable {G : Type} [Group G]

theorem mem_conjugate_iff {H : Subgroup G} {g x : G} : x ∈ conjugate H g ↔ g * x * g⁻¹ ∈ H := by
  unfold conjugate
  constructor
  · rintro ⟨y, hy, rfl⟩
    have : g * (MulAut.conj g⁻¹).toMonoidHom y * g⁻¹ = y := by
      show g * (MulAut.conj g⁻¹ y) * g⁻¹ = y
      simp only [MulAut.conj_apply]
      group
    rw [this]
    exact hy
  · intro h
    refine ⟨g * x * g⁻¹, h, ?_⟩
    show MulAut.conj g⁻¹ (g * x * g⁻¹) = x
    simp only [MulAut.conj_apply]
    group

theorem exists_elemAbelian_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (r : ℕ)
    (h : ∃ A : Subgroup X, CFSG.IsElementaryAbelian 2 ↥A ∧ Nat.card ↥A = 2 ^ r) :
    ∃ A : Subgroup Y, CFSG.IsElementaryAbelian 2 ↥A ∧ Nat.card ↥A = 2 ^ r := by
  obtain ⟨A, hA, hc⟩ := h
  refine ⟨A.map e.toMonoidHom, ?_, by rw [Subgroup.card_map_of_injective e.injective, hc]⟩
  exact @CFSG.IsElementaryAbelian.map 2 _ X Y _ _ A hA e.toMonoidHom

theorem pRank_two_eq_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) :
    pRank 2 X = pRank 2 Y := by
  unfold CFSG.pRank
  congr 1
  ext r
  exact ⟨exists_elemAbelian_of_mulEquiv e r, exists_elemAbelian_of_mulEquiv e.symm r⟩

theorem pRank_conjugate (H : Subgroup G) (g : G) : pRank 2 ↥(conjugate H g) = pRank 2 ↥H :=
  (pRank_two_eq_of_mulEquiv (Subgroup.equivMapOfInjective H (MulAut.conj g⁻¹).toMonoidHom
    (MulAut.conj g⁻¹).injective)).symm

theorem isElementaryAbelian_conjugate {U : Subgroup G} (h : CFSG.IsElementaryAbelian 2 ↥U) (g : G) :
    CFSG.IsElementaryAbelian 2 ↥(conjugate U g) := by
  have : CFSG.IsElementaryAbelian 2 ↥U := h
  exact CFSG.IsElementaryAbelian.map (A := U) (MulAut.conj g⁻¹).toMonoidHom

theorem isElementaryAbelian_of_le {B Q : Subgroup G} (hB : CFSG.IsElementaryAbelian 2 ↥B) (hQ : Q ≤ B) :
    CFSG.IsElementaryAbelian 2 ↥Q := by
  have : CFSG.IsElementaryAbelian 2 ↥B := hB
  have hcomm : ∀ u ∈ B, ∀ v ∈ B, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (mul_comm' (⟨u, hu⟩ : ↥B) ⟨v, hv⟩)
  have hsq : ∀ u ∈ B, u * u = 1 := fun u hu => by
    have h := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := B) u hu
    rwa [sq] at h
  have : IsMulCommutative ↥Q := ⟨⟨fun a b => Subtype.ext (hcomm a (hQ a.2) b (hQ b.2))⟩⟩
  refine { toIsMulCommutative := inferInstance, exponent_dvd_p := ?_ }
  refine Monoid.exponent_dvd_of_forall_pow_eq_one fun a => ?_
  apply Subtype.ext
  simp [sq, hsq a (hQ a.2)]

theorem exists_conj_of_mul_mem {H : Type*} [Group H] (N : Subgroup H) (hN : Odd (Nat.card ↥N))
    {a b : H} (ha : a * a = 1) (hb : b * b = 1) (h : a * b ∈ N) : ∃ y ∈ N, y * b * y⁻¹ = a := by
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  set t := a * b with ht
  have hodd : Odd (orderOf t) := Odd.of_dvd_nat hN (Subgroup.orderOf_dvd_natCard N h)
  obtain ⟨j, hj⟩ := exists_pow_eq_self_of_coprime (Nat.coprime_two_left.2 hodd)
  have hinv : t⁻¹ = b * a := by rw [ht, mul_inv_rev, ha', hb']
  have hconj : b * t * b⁻¹ = t⁻¹ := by
    rw [hinv, ht, hb']
    calc b * (a * b) * b = b * a * (b * b) := by group
      _ = b * a := by rw [hb, mul_one]
  have hy : (t ^ j) * (t ^ j) = t := by
    rw [← pow_add, ← two_mul, pow_mul, hj]
  have hconjy : b * t ^ j * b⁻¹ = (t ^ j)⁻¹ := by
    rw [← conj_pow, hconj, inv_pow]
  have hconjy' : b * (t ^ j)⁻¹ * b⁻¹ = t ^ j := by
    have := congrArg (fun z => z⁻¹) hconjy
    simpa [mul_assoc] using this
  have hcomm : t ^ j * b = b * (t ^ j)⁻¹ := (mul_inv_eq_iff_eq_mul.1 hconjy').symm
  refine ⟨t ^ j, N.pow_mem h j, ?_⟩
  calc t ^ j * b * (t ^ j)⁻¹ = b * (t ^ j)⁻¹ * (t ^ j)⁻¹ := by rw [hcomm]
    _ = b * ((t ^ j) * (t ^ j))⁻¹ := by rw [mul_inv_rev, mul_assoc]
    _ = b * (b * a) := by rw [hy, hinv]
    _ = a := by rw [← mul_assoc, hb, one_mul]

theorem cor2_a_C {M : Subgroup G} (h2 : Stage2Concl2C M) (X B : Subgroup G) (hXM : X ≤ M)
    (hB : InU0C M B) (hBX : B ≤ X) : normalizer (X : Set G) ≤ M := by
  intro g hg
  refine h2 B hB g ?_
  rintro _ ⟨b, hb, rfl⟩
  refine hXM ?_
  have hb' := (mem_normalizer_iff''.1 hg b).1 (hBX hb)
  simpa [MulAut.conj_apply] using hb'

theorem cor2_b_C {M : Subgroup G} (h2 : Stage2Concl2C M) (X B : Subgroup G) (hB : InU0C M B)
    (hsub : (B.subgroupOf X).IsSubnormal) (hBX : B ≤ X) : X ≤ M := by
  have key : ∀ H : Subgroup ↥X, H.IsSubnormal → B ≤ H.map X.subtype → H.map X.subtype ≤ M →
      X ≤ M := by
    intro H hH
    induction hH with
    | top =>
      intro _ hM
      simpa [Subgroup.map_top, Subgroup.range_subtype] using hM
    | step H K h_le _ hN ih =>
      intro hBH hHM
      refine ih (hBH.trans (Subgroup.map_mono h_le)) ?_
      have hKN : K ≤ normalizer (H : Set ↥X) := (normal_subgroupOf_iff_le_normalizer h_le).1 hN
      calc K.map X.subtype ≤ (normalizer (H : Set ↥X)).map X.subtype := Subgroup.map_mono hKN
        _ ≤ normalizer ((H.map X.subtype : Subgroup G) : Set G) := Subgroup.le_normalizer_map _
        _ ≤ M := cor2_a_C h2 _ B hHM hB hBH
  have hmap : (B.subgroupOf X).map X.subtype = B := Subgroup.map_subgroupOf_eq_of_le hBX
  exact key _ hsub hmap.ge (hmap.le.trans hB.1.1)

theorem cor2_c_C [Finite G] {M : Subgroup G} (h2 : Stage2Concl2C M) (X B : Subgroup G)
    (hX : IsPGroup 2 ↥X) (hB : InU0C M B) (hBX : B ≤ X) : X ≤ M :=
  cor2_b_C h2 X B hB (CFSG.BaerSuzuki.Helpers.subgroup_isSubnormal_of_isPGroup hX _) hBX

end T4Basic

section T0

variable {G : Type} [Group G]

theorem inU0C_conj {M B : Subgroup G} (hB : InU0C M B) {m : G} (hm : m ∈ M) :
    InU0C M (conjugate B m) := by
  obtain ⟨⟨hBM, hBel, hr2⟩, hrk, hγ⟩ := hB
  have hrank : pRank 2 ↥(conjugate B m) = pRank 2 ↥B := T4Basic.pRank_conjugate B m
  have hle : conjugate B m ≤ M := fun x hx => by
    have h1 := hBM (T4Basic.mem_conjugate_iff.1 hx)
    have := M.mul_mem (M.mul_mem (M.inv_mem hm) h1) hm
    simpa [mul_assoc] using this
  refine ⟨⟨hle, T4Basic.isElementaryAbelian_conjugate hBel m, hrank ▸ hr2⟩, hrank ▸ hrk, ?_⟩
  rw [hrank]
  refine iSup₂_le fun Q hQ => iSup_le fun hk g hg => ?_
  set Q' : Subgroup G := conjugate Q m⁻¹ with hQ'
  have hmemQ' : ∀ x : G, x ∈ Q' ↔ m⁻¹ * x * m ∈ Q := fun x => by
    rw [hQ', T4Basic.mem_conjugate_iff, inv_inv]
  have hQ'B : Q' ≤ B := fun x hx => by
    have h1 := T4Basic.mem_conjugate_iff.1 (hQ ((hmemQ' x).1 hx))
    simpa [mul_assoc] using h1
  have hk' : pRank 2 ↥B - 1 ≤ pRank 2 ↥Q' := by
    rw [hQ', T4Basic.pRank_conjugate]
    exact hk
  have hc : m * g * m⁻¹ ∈ centralizer (Q' : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 := Subgroup.mem_centralizer_iff.1 hg _ ((hmemQ' x).1 hx)
    have e : x = m * (m⁻¹ * x * m) * m⁻¹ := by group
    rw [e]
    calc m * (m⁻¹ * x * m) * m⁻¹ * (m * g * m⁻¹)
        = m * ((m⁻¹ * x * m) * g) * m⁻¹ := by group
      _ = m * (g * (m⁻¹ * x * m)) * m⁻¹ := by rw [h1]
      _ = m * g * m⁻¹ * (m * (m⁻¹ * x * m) * m⁻¹) := by group
  have hmem : m * g * m⁻¹ ∈ M :=
    hγ ((le_iSup₂_of_le Q' hQ'B (le_iSup_of_le hk' le_rfl) :
      centralizer (Q' : Set G) ≤ gammaKC 2 B (pRank 2 ↥B - 1)) hc)
  have := M.mul_mem (M.mul_mem (M.inv_mem hm) hmem) hm
  simpa [mul_assoc] using this

theorem le_M_of_normal_of_inU0C [Finite G] {M B : Subgroup G} (h2 : Stage2Concl2C M)
    (hB : InU0C M B) {N X : Subgroup G} (hNX : N ≤ X) (hN : (N.subgroupOf X).Normal)
    (hBN : B ≤ N) (hNM : N ≤ M) : X ≤ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hB.1.2.1
  have hBp : IsPGroup 2 ↥B := IsElementaryAbelian.isPGroup 2 ↥B
  have hBp' : IsPGroup 2 (B.subgroupOf N) := hBp.comap_subtype
  obtain ⟨T, hT⟩ := hBp'.exists_le_sylow
  have hPN : IsSylowOf 2 ((T : Subgroup N).map N.subtype) N := ⟨T, rfl⟩
  have hBP : B ≤ (T : Subgroup N).map N.subtype := fun a ha =>
    ⟨⟨a, hBN ha⟩, hT (Subgroup.mem_subgroupOf.mpr ha), rfl⟩
  have hPM : (T : Subgroup N).map N.subtype ≤ M := T4Basic.cor2_c_C h2 _ B hPN.isPGroup hB hBP
  have hNP : normalizer (((T : Subgroup N).map N.subtype : Subgroup G) : Set G) ≤ M :=
    T4Basic.cor2_a_C h2 _ B hPM hB hBP
  have hX : N ⊔ (X ⊓ normalizer (((T : Subgroup N).map N.subtype : Subgroup G) : Set G)) = X :=
    CFSG.Semidihedral.Local.sup_inf_normalizer_eq hNX hN hPN.le (by simpa using hPN.card_eq)
  rw [← hX]
  exact sup_le hNM (inf_le_right.trans hNP)

theorem inU0C_of_four_subgroups {M B : Subgroup G} (hBM : B ≤ M)
    (hB : CFSG.IsElementaryAbelian 2 ↥B) (h8 : Nat.card ↥B = 8)
    (hD : ∀ D : Subgroup G, D ≤ B → Nat.card ↥D = 4 → centralizer (D : Set G) ≤ M) :
    InU0C M B := by
  have hfin : Finite ↥B := Nat.finite_of_card_ne_zero (by omega)
  have : CFSG.IsElementaryAbelian 2 ↥B := hB
  have hr3 : pRank 2 ↥B = 3 := pRank_eq_of_card_eq_pow one_lt_two (k := 3) (by rw [h8]; norm_num)
  refine ⟨⟨hBM, hB, by omega⟩, Or.inr hr3, ?_⟩
  rw [hr3]
  refine iSup₂_le fun Q hQ => iSup_le fun hk => ?_
  have hQel : CFSG.IsElementaryAbelian 2 ↥Q := T4Basic.isElementaryAbelian_of_le hB hQ
  have hQfin : Finite ↥Q := Finite.Set.subset (B : Set G) hQ
  obtain ⟨s, hs⟩ := (CFSG.IsElementaryAbelian.isPGroup 2 ↥Q).exists_card_eq
  have hs2 : 2 ≤ s := by
    have := pRank_eq_of_card_eq_pow one_lt_two hs
    omega
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime_of_le_card Nat.prime_two
    (CFSG.IsElementaryAbelian.isPGroup 2 ↥Q) (n := 2) (by rw [hs]; exact Nat.pow_le_pow_right two_pos hs2)
  have hDQ : K.map Q.subtype ≤ Q := fun x hx => by
    obtain ⟨y, -, rfl⟩ := hx
    exact y.2
  have hcard : Nat.card ↥(K.map Q.subtype) = 4 := by
    rw [Subgroup.card_map_of_injective Q.subtype_injective, hK]
    norm_num
  exact (Subgroup.centralizer_le hDQ).trans (hD _ (hDQ.trans hQ) hcard)

theorem exists_conj_of_isConj_bar [Finite G] {M : Subgroup G} {v w : G} (hv : v ∈ M) (hw : w ∈ M)
    (hv2 : orderOf v = 2) (hw2 : orderOf w = 2)
    (hc : IsConj (QuotientGroup.mk (⟨v, hv⟩ : ↥M) : Mbar M) (QuotientGroup.mk (⟨w, hw⟩ : ↥M))) :
    ∃ m ∈ M, m⁻¹ * w * m = v := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNodd : Odd (Nat.card ↥(pPrimeCore 2 ↥M)) :=
    Nat.coprime_two_left.1 (pPrimeCore_coprime_card (p := 2) (G := ↥M))
  obtain ⟨cb, hcb⟩ := isConj_iff.1 hc
  obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective cb
  have hsq : ∀ {x : G} (hx : x ∈ M), orderOf x = 2 → (⟨x, hx⟩ : ↥M) * ⟨x, hx⟩ = 1 := by
    intro x hx h2
    apply Subtype.ext
    have := pow_orderOf_eq_one x
    rw [h2, sq] at this
    exact this
  set a : ↥M := ⟨v, hv⟩ with ha
  set b : ↥M := ⟨w, hw⟩ with hb
  have ha2 : (c * a * c⁻¹) * (c * a * c⁻¹) = 1 := by
    have : a * a = 1 := hsq hv hv2
    calc (c * a * c⁻¹) * (c * a * c⁻¹) = c * (a * a) * c⁻¹ := by group
      _ = 1 := by rw [this]; group
  have hb2 : b * b = 1 := hsq hw hw2
  have hmk : (QuotientGroup.mk (c * a * c⁻¹) : Mbar M) = QuotientGroup.mk b := by
    rw [← hcb]
    simp
  have hmem : (c * a * c⁻¹) * b ∈ pPrimeCore 2 ↥M := by
    have h1 := QuotientGroup.eq.1 hmk
    rwa [inv_eq_of_mul_eq_one_right ha2] at h1
  obtain ⟨y, -, hy⟩ := T4Basic.exists_conj_of_mul_mem _ hNodd ha2 hb2 hmem
  refine ⟨((y⁻¹ * c : ↥M) : G), (y⁻¹ * c).2, ?_⟩
  have e : (y⁻¹ * c)⁻¹ * b * (y⁻¹ * c) = a := by
    calc (y⁻¹ * c)⁻¹ * b * (y⁻¹ * c) = c⁻¹ * (y * b * y⁻¹) * c := by group
      _ = a := by rw [hy]; group
  have := congrArg (fun z : ↥M => (z : G)) e
  simpa using this

end T0

end CFSG.GH74.Generic.BProg.B2.T4
