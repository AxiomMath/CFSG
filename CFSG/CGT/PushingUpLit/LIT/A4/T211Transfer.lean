module

public import CFSG.CGT.PushingUpLit.LIT.A4.T211Endgame
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.CGT.PushingUpLit.T211

open Subgroup MulAction

section Setup

variable {G : Type*} [Group G]

theorem z2_sq (z : Z2) : z ^ 2 = 1 := by revert z; decide

theorem z2_pow_odd (z : Z2) {k : ℕ} (hk : Odd k) : z ^ k = z := by
  obtain ⟨j, rfl⟩ := hk
  rw [pow_succ, pow_mul, pow_two, z2_mul_self, one_pow, one_mul]

theorem exists_hom_of_relIndex_two {M M₁ : Subgroup G} (h2 : M₁.relIndex M = 2) :
    ∃ μ : M →* Z2, ∀ m : M, μ m = 1 ↔ (m : G) ∈ M₁ := by
  have hidx : (M₁.subgroupOf M).index = 2 := h2
  have : (M₁.subgroupOf M).Normal := Subgroup.normal_of_index_eq_two hidx
  have hcard : Nat.card (M ⧸ M₁.subgroupOf M) = 2 := by
    rw [← Subgroup.index_eq_card, hidx]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let e : M ⧸ M₁.subgroupOf M ≃* Z2 :=
    mulEquivOfPrimeCardEq hcard (CFSG.RankThree.Transfer.card_multiplicative_zmod (p := 2))
  refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' _), fun m => ?_⟩
  rw [MonoidHom.coe_comp, Function.comp_apply, QuotientGroup.mk'_apply, MulEquiv.coe_toMonoidHom,
    map_eq_one_iff e e.injective, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

theorem exists_ext_ne_one {M M₁ S : Subgroup G} (h₁ : M₁ ≤ M) (h2 : M₁.relIndex M = 2)
    (hSM : S ≤ M) (hSodd : ¬ 2 ∣ S.relIndex M) (μ : M →* Z2)
    (hμ : ∀ m : M, μ m = 1 ↔ (m : G) ∈ M₁) : ∃ s ∈ S, ext μ s ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hSM₁ : S ≤ M₁ := by
    intro s hs
    have h1 := hcon s hs
    rw [ext_of_mem μ (hSM hs)] at h1
    exact (hμ ⟨s, hSM hs⟩).mp h1
  have h3 := Subgroup.relIndex_mul_relIndex S M₁ M hSM₁ h₁
  rw [h2] at h3
  exact hSodd ⟨S.relIndex M₁, by rw [← h3]; ring⟩

theorem exists_min_order {S : Subgroup G} {M : Subgroup G} (μ : M →* Z2)
    (hS : ∃ s ∈ S, ext μ s ≠ 1) :
    ∃ x ∈ S, ext μ x ≠ 1 ∧ ∀ s ∈ S, ext μ s ≠ 1 → orderOf x ≤ orderOf s := by
  classical
  obtain ⟨s0, hs0, h0⟩ := hS
  have hex : ∃ n, ∃ s ∈ S, ext μ s ≠ 1 ∧ orderOf s = n := ⟨_, s0, hs0, h0, rfl⟩
  obtain ⟨x, hxS, hxe, hxn⟩ := Nat.find_spec hex
  refine ⟨x, hxS, hxe, fun s hs he => ?_⟩
  rw [hxn]
  exact Nat.find_min' hex ⟨s, hs, he, rfl⟩

theorem orderOf_le_of_ext_ne_one [Finite G] {M S : Subgroup G} (hSM : S ≤ M) (hS2 : IsPGroup 2 S)
    (hSodd : ¬ 2 ∣ S.relIndex M) (μ : M →* Z2) {x : G}
    (hmin : ∀ s ∈ S, ext μ s ≠ 1 → orderOf x ≤ orderOf s) {m : G} (hmM : m ∈ M)
    (hm : ext μ m ≠ 1) : orderOf x ≤ orderOf m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn0 : orderOf m ≠ 0 := (orderOf_pos m).ne'
  obtain ⟨e, k, hk, hnk⟩ := Nat.exists_eq_two_pow_mul_odd hn0
  have hk0 : k ≠ 0 := hk.pos.ne'
  have hkdvd : k ∣ orderOf m := ⟨2 ^ e, by rw [hnk, mul_comm]⟩
  have hord2 : orderOf (m ^ k) = 2 ^ e := by
    rw [orderOf_pow_of_dvd hk0 hkdvd, hnk, Nat.mul_div_cancel _ hk.pos]
  have hm2M : m ^ k ∈ M := M.pow_mem hmM k
  have hext : ext μ (m ^ k) = ext μ m := by
    rw [ext_of_mem μ hm2M, ext_of_mem μ hmM]
    have : (⟨m ^ k, hm2M⟩ : M) = (⟨m, hmM⟩ : M) ^ k := rfl
    rw [this, map_pow, z2_pow_odd _ hk]
  have hS2' : IsPGroup 2 (S.subgroupOf M) :=
    hS2.of_equiv (Subgroup.subgroupOfEquivOfLe hSM).symm
  let S' : Sylow 2 M := IsPGroup.toSylow hS2' hSodd
  let m' : M := ⟨m ^ k, hm2M⟩
  have hm'ord : orderOf m' = 2 ^ e := by
    rw [Subgroup.orderOf_mk, hord2]
  have hQ : IsPGroup 2 (zpowers m') :=
    IsPGroup.of_card (n := e) (by rw [Nat.card_zpowers, hm'ord])
  obtain ⟨P, hP⟩ := hQ.exists_le_sylow
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq M P S'
  have hm'P : m' ∈ (P : Subgroup M) := hP (mem_zpowers m')
  have hyS' : y * m' * y⁻¹ ∈ (S' : Subgroup M) := by
    rw [← hy, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
    exact ⟨m', hm'P, by simp [MulAut.conj_apply]⟩
  have hyS : (y : G) * m ^ k * (y : G)⁻¹ ∈ S := by
    have h : y * m' * y⁻¹ ∈ S.subgroupOf M := hyS'
    rw [Subgroup.mem_subgroupOf] at h
    simpa using h
  have hext2 : ext μ ((y : G) * m ^ k * (y : G)⁻¹) = ext μ m := by
    rw [ext_conj μ y.2 hm2M, hext]
  have hle := hmin _ hyS (by rw [hext2]; exact hm)
  have hconj : orderOf ((y : G) * m ^ k * (y : G)⁻¹) = orderOf (m ^ k) := by
    simpa using CFSG.RankThree.Transfer.orderOf_conj (y : G)⁻¹ (m ^ k)
  rw [hconj, hord2] at hle
  calc orderOf x ≤ 2 ^ e := hle
    _ ≤ 2 ^ e * k := Nat.le_mul_of_pos_right _ hk.pos
    _ = orderOf m := hnk.symm

section Parity

theorem prod_eq_one_iff_even {α : Type*} [Fintype α] (f : α → Z2) :
    ∏ a, f a = 1 ↔ Even (Finset.univ.filter fun a => f a ≠ 1).card := by
  classical
  have key : ∀ z : Z2, Multiplicative.toAdd z = if z ≠ 1 then 1 else 0 := by decide
  have h1 : Multiplicative.toAdd (∏ a, f a) =
      ((Finset.univ.filter fun a => f a ≠ 1).card : ZMod 2) := by
    rw [toAdd_prod]
    simp_rw [key]
    rw [Finset.sum_boole]
  rw [← toAdd_eq_zero, h1, even_iff_two_dvd, ZMod.natCast_eq_zero_iff]

open scoped Classical in
theorem exists_odd_orbit {H : Type*} [Group H] {Ω : Type*} [MulAction H Ω] [Finite Ω]
    (F : Finset Ω) (hF : Even F.card) {b : Ω} (hbF : b ∈ F) (hb : ∀ h : H, h • b = b) :
    ∃ X₀ ∈ F, X₀ ≠ b ∧ Odd (F.filter fun Y => Y ∈ MulAction.orbit H X₀).card := by
  classical
  have : Fintype Ω := Fintype.ofFinite Ω
  by_contra hcon
  push Not at hcon
  have hb' : ∀ Y₀ : Ω, Y₀ ≠ b → b ∉ MulAction.orbit H Y₀ := by
    rintro Y₀ hY₀ ⟨h, hh⟩
    apply hY₀
    have hh' : h • Y₀ = b := hh
    have : Y₀ = h⁻¹ • b := by rw [← hh', inv_smul_smul]
    rw [this]
    exact hb h⁻¹
  have hodd : Odd (F.erase b).card := by
    have h1 := Finset.card_erase_add_one hbF
    rcases hF with ⟨k, hk⟩
    exact ⟨k - 1, by omega⟩
  have : Fintype (MulAction.orbitRel.Quotient H Ω) := Fintype.ofFinite _
  have hsum := Finset.card_eq_sum_card_fiberwise (s := F.erase b) (t := Finset.univ)
    (f := fun Y : Ω => (Quotient.mk'' Y : MulAction.orbitRel.Quotient H Ω))
    (fun _ _ => Finset.mem_univ _)
  have hev : ∀ q ∈ (Finset.univ : Finset (MulAction.orbitRel.Quotient H Ω)),
      Even ((F.erase b).filter fun Y =>
        (Quotient.mk'' Y : MulAction.orbitRel.Quotient H Ω) = q).card := by
    intro q _
    by_cases hne : ((F.erase b).filter fun Y =>
        (Quotient.mk'' Y : MulAction.orbitRel.Quotient H Ω) = q).Nonempty
    · obtain ⟨Y₀, hY₀⟩ := hne
      rw [Finset.mem_filter, Finset.mem_erase] at hY₀
      obtain ⟨⟨hY₀b, hY₀F⟩, hY₀q⟩ := hY₀
      have hfib : ((F.erase b).filter fun Y =>
          (Quotient.mk'' Y : MulAction.orbitRel.Quotient H Ω) = q) =
            F.filter fun Y => Y ∈ MulAction.orbit H Y₀ := by
        ext Y
        simp only [Finset.mem_filter, Finset.mem_erase]
        constructor
        · rintro ⟨⟨hYb, hYF⟩, hYq⟩
          refine ⟨hYF, ?_⟩
          rw [← hY₀q] at hYq
          exact (MulAction.orbitRel_apply.mp (Quotient.exact hYq))
        · rintro ⟨hYF, hYo⟩
          refine ⟨⟨?_, hYF⟩, ?_⟩
          · rintro rfl
            exact hb' Y₀ hY₀b hYo
          · rw [← hY₀q]
            exact Quotient.sound (MulAction.orbitRel_apply.mpr hYo)
      rw [hfib]
      exact Nat.not_odd_iff_even.mp (hcon Y₀ hY₀F hY₀b)
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      rw [hne]; simp
  have := Finset.even_sum _ hev
  rw [← hsum] at this
  exact (Nat.not_even_iff_odd.mpr hodd) this

end Parity

end Setup

section Transfer

variable {G : Type*} [Group G] [Finite G]

theorem transfer_eq_one (hG : ∀ (N : Subgroup G) [N.Normal], IsPGroup 2 (G ⧸ N) → N = ⊤)
    {M : Subgroup G} (μ : M →* Z2) (g : G) : μ.transfer g = 1 := by
  have hnorm : (μ.transfer).ker.Normal := MonoidHom.normal_ker _
  have hker : (μ.transfer).ker = ⊤ := by
    apply hG
    intro y
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective y
    refine ⟨1, ?_⟩
    rw [pow_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact MonoidHom.mem_ker.mpr ((map_pow μ.transfer a 2).trans (z2_sq _))
  have : g ∈ (μ.transfer).ker := hker ▸ mem_top g
  exact this

theorem even_card_odd_cosets (hG : ∀ (N : Subgroup G) [N.Normal], IsPGroup 2 (G ⧸ N) → N = ⊤)
    {M : Subgroup G} (μ : M →* Z2) {x : G}
    (hmin : ∀ h : M, orderOf (h : G) < orderOf x → μ h = 1) [Fintype (G ⧸ M)]
    [DecidableEq (G ⧸ M)] :
    Even (Finset.univ.filter fun X : G ⧸ M =>
      x • X = X ∧ CFSG.RankThree.Transfer.cosetValue μ x X ≠ 1).card := by
  have h1 := CFSG.RankThree.Transfer.transfer_eq_prod_fixed_of_orderOf_lt μ x hmin
  rw [transfer_eq_one hG μ x] at h1
  have h2 := (prod_eq_one_iff_even _).mp h1.symm
  convert h2 using 2
  ext X
  by_cases hx : x • X = X
  · simp [hx]
  · simp [hx]
    rfl

omit [Finite G] in
theorem fixed_odd_iff {M : Subgroup G} (μ : M →* Z2) (x g : G) :
    (x • ((g : G) : G ⧸ M) = (g : G ⧸ M) ∧
      CFSG.RankThree.Transfer.cosetValue μ x (g : G ⧸ M) ≠ 1) ↔ ext μ (g⁻¹ * x * g) ≠ 1 := by
  have hfix : x • ((g : G) : G ⧸ M) = (g : G ⧸ M) ↔ g⁻¹ * x * g ∈ M :=
    CFSG.RankThree.Transfer.smul_coe_eq_iff
  by_cases hm : g⁻¹ * x * g ∈ M
  · rw [hfix, CFSG.RankThree.Transfer.cosetValue_coe μ hm, ext_of_mem μ hm]
    exact ⟨fun h => h.2, fun h => ⟨hm, h⟩⟩
  · rw [hfix]
    have h1 : ext μ (g⁻¹ * x * g) = 1 := by simp [ext, hm]
    rw [h1]
    simp [hm]

end Transfer

section Data

variable {G : Type*} [Group G] {M : Subgroup G} (R : Subgroup G)

theorem mem_stabilizer_coset (h : G) (r : R) :
    r ∈ MulAction.stabilizer R ((h : G) : G ⧸ M) ↔ h⁻¹ * (r : G) * h ∈ M := by
  rw [MulAction.mem_stabilizer_iff]
  have e1 : ((r : R) • ((h : G) : G ⧸ M)) = (((r : G) * h : G) : G ⧸ M) := rfl
  rw [e1, QuotientGroup.eq]
  have e : ((r : G) * h)⁻¹ * h = (h⁻¹ * (r : G) * h)⁻¹ := by group
  rw [e, M.inv_mem_iff]

@[expose] def phiR (μ : M →* Z2) (h : G) : MulAction.stabilizer R ((h : G) : G ⧸ M) →* Z2 :=
  MonoidHom.mk' (fun t => μ ⟨h⁻¹ * ((t : R) : G) * h, (mem_stabilizer_coset R h t).mp t.2⟩)
    (fun a b => by
      rw [← map_mul]
      congr 1
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      group)

theorem ext_phiR (μ : M →* Z2) (h : G) (r : R) :
    ext (phiR R μ h) r = ext μ (h⁻¹ * (r : G) * h) := by
  by_cases hr : r ∈ MulAction.stabilizer R ((h : G) : G ⧸ M)
  · rw [ext_of_mem _ hr, ext_of_mem μ ((mem_stabilizer_coset R h r).mp hr)]
    rfl
  · have h1 : ext (phiR R μ h) r = 1 := by simp [ext, hr]
    have h2 : ext μ (h⁻¹ * (r : G) * h) = 1 := by
      have : h⁻¹ * (r : G) * h ∉ M := fun hm => hr ((mem_stabilizer_coset R h r).mpr hm)
      simp [ext, this]
    rw [h1, h2]

theorem mem_oddFixed_iff (μ : M →* Z2) (h : G) (x ρ : R) :
    ((ρ : R) : R ⧸ MulAction.stabilizer R ((h : G) : G ⧸ M)) ∈ oddFixed (phiR R μ h) x ↔
      ext μ (((ρ : G) * h)⁻¹ * (x : G) * ((ρ : G) * h)) ≠ 1 := by
  have key : ∀ y : R, ext (phiR R μ h) y = ext μ (h⁻¹ * (y : G) * h) := ext_phiR R μ h
  constructor
  · rintro ⟨r, hr, hne⟩
    have ht : r⁻¹ * ρ ∈ MulAction.stabilizer R ((h : G) : G ⧸ M) := QuotientGroup.eq.mp hr
    have hy : r⁻¹ * x * r ∈ MulAction.stabilizer R ((h : G) : G ⧸ M) := mem_of_ext_ne_one hne
    have h1 : ρ⁻¹ * x * ρ = (r⁻¹ * ρ)⁻¹ * (r⁻¹ * x * r) * (r⁻¹ * ρ) := by group
    have h2 : ext (phiR R μ h) (ρ⁻¹ * x * ρ) ≠ 1 := by
      rw [h1, ext_conj' _ ht hy]; exact hne
    rw [key] at h2
    have e : h⁻¹ * ((ρ⁻¹ * x * ρ : R) : G) * h = ((ρ : G) * h)⁻¹ * (x : G) * ((ρ : G) * h) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
    rwa [e] at h2
  · intro hne
    refine ⟨ρ, rfl, ?_⟩
    rw [key]
    have e : h⁻¹ * ((ρ⁻¹ * x * ρ : R) : G) * h = ((ρ : G) * h)⁻¹ * (x : G) * ((ρ : G) * h) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
    rwa [e]

theorem card_oddFixed (μ : M →* Z2) (h : G) (x : R) (F' : Set (G ⧸ M))
    (hF' : ∀ g : G, (g : G ⧸ M) ∈ F' ↔ ext μ (g⁻¹ * (x : G) * g) ≠ 1) :
    Nat.card (oddFixed (phiR R μ h) x) =
      Nat.card {Y : G ⧸ M // Y ∈ F' ∧ Y ∈ MulAction.orbit R ((h : G) : G ⧸ M)} := by
  let e := MulAction.orbitEquivQuotientStabilizer R ((h : G) : G ⧸ M)
  let e1 : {Z // Z ∈ oddFixed (phiR R μ h) x} ≃
      {Y : MulAction.orbit R ((h : G) : G ⧸ M) // (Y : G ⧸ M) ∈ F'} :=
    Equiv.subtypeEquiv e.symm (fun Z => by
      induction Z using QuotientGroup.induction_on with
      | H ρ =>
        have : ((e.symm (ρ : R ⧸ _) : MulAction.orbit R ((h : G) : G ⧸ M)) : G ⧸ M) =
            ((((ρ : G) * h : G)) : G ⧸ M) := rfl
        rw [this, hF', mem_oddFixed_iff])
  let e2 : {Y : MulAction.orbit R ((h : G) : G ⧸ M) // (Y : G ⧸ M) ∈ F'} ≃
      {Y : G ⧸ M // Y ∈ F' ∧ Y ∈ MulAction.orbit R ((h : G) : G ⧸ M)} :=
    (Equiv.subtypeSubtypeEquivSubtypeInter (fun Y => Y ∈ MulAction.orbit R ((h : G) : G ⧸ M))
      (fun Y => Y ∈ F')).trans (Equiv.subtypeEquivRight fun Y => and_comm)
  exact Nat.card_congr (e1.trans e2)

theorem normal_subgroupOf_of_le {A S R : Subgroup G} (hRS : R ≤ S)
    (hAn : (A.subgroupOf S).Normal) : (A.subgroupOf R).Normal where
  conj_mem n hn g := by
    have hn' : ((⟨(n : G), hRS n.2⟩ : S) : G) ∈ A := Subgroup.mem_subgroupOf.mp hn
    have h1 := hAn.conj_mem ⟨(n : G), hRS n.2⟩ (Subgroup.mem_subgroupOf.mpr hn')
      ⟨(g : G), hRS g.2⟩
    rw [Subgroup.mem_subgroupOf] at h1 ⊢
    simpa using h1

theorem sup_subgroupOf_zpowers_eq_top (A : Subgroup G) (x : G) (hx : x ∈ A ⊔ zpowers x) :
    (A.subgroupOf (A ⊔ zpowers x)) ⊔ zpowers (⟨x, hx⟩ : ↥(A ⊔ zpowers x)) = ⊤ := by
  apply Subgroup.map_injective (A ⊔ zpowers x).subtype_injective
  rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, MonoidHom.map_zpowers,
    inf_of_le_left le_sup_left, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rfl

theorem mem_of_map_conj_eq {A M : Subgroup G} (hN : Subgroup.normalizer (A : Set G) ≤ M) {g m : G}
    (hm : m ∈ M) (h : A.map (MulAut.conj g).toMonoidHom = A.map (MulAut.conj m).toMonoidHom) :
    g ∈ M := by
  have hmem : m⁻¹ * g ∈ Subgroup.normalizer (A : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · intro hn
      have h1 : g * n * g⁻¹ ∈ A.map (MulAut.conj g).toMonoidHom :=
        ⟨n, hn, by simp [MulAut.conj_apply]⟩
      rw [h] at h1
      obtain ⟨a, ha, hae⟩ := h1
      have : a = m⁻¹ * g * n * (m⁻¹ * g)⁻¹ := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hae
        have := congrArg (fun y => m⁻¹ * y * m) hae
        simpa [mul_assoc] using this
      rw [← this]; exact ha
    · intro hn
      have h1 : m * (m⁻¹ * g * n * (m⁻¹ * g)⁻¹) * m⁻¹ ∈ A.map (MulAut.conj m).toMonoidHom :=
        ⟨_, hn, by simp [MulAut.conj_apply]⟩
      rw [← h] at h1
      obtain ⟨a, ha, hae⟩ := h1
      have : a = n := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hae
        have := congrArg (fun y => g⁻¹ * y * g) hae
        simpa [mul_assoc] using this
      rw [← this]; exact ha
  have := hN hmem
  simpa using M.mul_mem hm this

end Data

section Main

variable {G : Type*} [Group G] [Finite G]

theorem harada_transfer_211
    (hG : ∀ (N : Subgroup G) [N.Normal], IsPGroup 2 (G ⧸ N) → N = ⊤)
    {M M₁ S A : Subgroup G} (h₁ : M₁ ≤ M) (h2 : M₁.relIndex M = 2) (hSM : S ≤ M)
    (hS2 : IsPGroup 2 S) (hSodd : ¬ 2 ∣ S.relIndex M) (hAS : A ≤ S)
    (hAn : (A.subgroupOf S).Normal) (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hA4 : ∀ a ∈ A, a ^ 4 = 1) (hN : Subgroup.normalizer (A : Set G) ≤ M)
    (hSyl : ∀ g : G, A.map (MulAut.conj g).toMonoidHom ≤ M →
      ∃ m ∈ M, A.map (MulAut.conj g).toMonoidHom = A.map (MulAut.conj m).toMonoidHom) :
    ∃ g : G, g ∉ M ∧ M.relIndex (A.map (MulAut.conj g).toMonoidHom) ≤ 2 ∧
      ¬ (A.map (MulAut.conj g).toMonoidHom ⊓ M ≤ M₁) := by
  classical
  obtain ⟨μ, hμ⟩ := exists_hom_of_relIndex_two h2
  obtain ⟨s₀, hs₀S, hs₀⟩ := exists_ext_ne_one h₁ h2 hSM hSodd μ hμ
  obtain ⟨x, hxS, hxe, hxmin⟩ := exists_min_order (S := S) μ ⟨s₀, hs₀S, hs₀⟩
  have hxM : x ∈ M := hSM hxS
  have hmin : ∀ m ∈ M, ext μ m ≠ 1 → orderOf x ≤ orderOf m :=
    fun m hmM hm => orderOf_le_of_ext_ne_one hSM hS2 hSodd μ hxmin hmM hm
  have hmin' : ∀ m : M, orderOf (m : G) < orderOf x → μ m = 1 := by
    intro m hlt
    by_contra hne
    have : ext μ (m : G) ≠ 1 := by rwa [ext_of_mem μ m.2]
    exact absurd (hmin _ m.2 this) (not_le.mpr hlt)
  let _ : Fintype (G ⧸ M) := Fintype.ofFinite _
  let F : Finset (G ⧸ M) := Finset.univ.filter fun X =>
    x • X = X ∧ CFSG.RankThree.Transfer.cosetValue μ x X ≠ 1
  have hFeven : Even F.card := even_card_odd_cosets hG μ hmin'
  have hFmem : ∀ g : G, ((g : G) : G ⧸ M) ∈ F ↔ ext μ (g⁻¹ * x * g) ≠ 1 := fun g => by
    rw [Finset.mem_filter]
    exact ⟨fun h => (fixed_odd_iff μ x g).mp h.2,
      fun h => ⟨Finset.mem_univ _, (fixed_odd_iff μ x g).mpr h⟩⟩
  let R : Subgroup G := A ⊔ zpowers x
  have hRS : R ≤ S := sup_le hAS (zpowers_le.mpr hxS)
  have hRM : R ≤ M := hRS.trans hSM
  have hxR : x ∈ R := mem_sup_right (mem_zpowers x)
  have hAR : A ≤ R := le_sup_left
  have hb₀F : ((1 : G) : G ⧸ M) ∈ F := (hFmem 1).mpr (by simpa using hxe)
  have hb₀fix : ∀ r : R, r • ((1 : G) : G ⧸ M) = ((1 : G) : G ⧸ M) := by
    intro r
    have e1 : (r • ((1 : G) : G ⧸ M)) = (((r : G) * 1 : G) : G ⧸ M) := rfl
    rw [e1, mul_one, QuotientGroup.eq]
    simpa using M.inv_mem (hRM r.2)
  obtain ⟨X₀, hX₀F, hX₀b, hodd⟩ := exists_odd_orbit (H := R) F hFeven hb₀F hb₀fix
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective X₀
  have hhM : h ∉ M := fun hm => hX₀b (QuotientGroup.eq.mpr (by simpa using M.inv_mem hm))
  let T : Subgroup R := MulAction.stabilizer R ((h : G) : G ⧸ M)
  let ϕ : T →* Z2 := phiR R μ h
  let xR : R := ⟨x, hxR⟩
  have hc : Odd (Nat.card (oddFixed ϕ xR)) := by
    have h1 := card_oddFixed R μ h xR (F : Set (G ⧸ M)) (fun g => by
      rw [Finset.mem_coe]; exact hFmem g)
    have h2' : Nat.card {Y : G ⧸ M // Y ∈ (F : Set (G ⧸ M)) ∧
        Y ∈ MulAction.orbit R ((h : G) : G ⧸ M)} =
          (F.filter fun Y => Y ∈ MulAction.orbit R ((h : G) : G ⧸ M)).card := by
      rw [← Nat.card_eq_finsetCard]
      exact Nat.card_congr (Equiv.subtypeEquivRight (fun Y => by simp [Finset.mem_filter]))
    rw [h1, h2']
    exact hodd
  have hT : T ≠ ⊤ := by
    intro hTtop
    have hAh : A.map (MulAut.conj h⁻¹).toMonoidHom ≤ M := by
      rintro _ ⟨a, ha, rfl⟩
      have hmem : (⟨a, hAR ha⟩ : R) ∈ T := hTtop ▸ mem_top _
      have := (mem_stabilizer_coset R h ⟨a, hAR ha⟩).mp hmem
      simpa [MulAut.conj_apply] using this
    obtain ⟨m, hm, hAm⟩ := hSyl h⁻¹ hAh
    exact hhM (by simpa using M.inv_mem (mem_of_map_conj_eq hN hm hAm))
  have hd : ∀ t ∈ T, orderOf t < orderOf xR → ext ϕ t = 1 := by
    intro t _ hlt
    rw [ext_phiR]
    by_contra hne
    have hle := hmin _ ((by
      by_contra hm
      exact hne (by simp [ext, hm])) : h⁻¹ * (t : G) * h ∈ M) hne
    have hord : orderOf (h⁻¹ * (t : G) * h) = orderOf t := by
      rw [CFSG.RankThree.Transfer.orderOf_conj, Subgroup.orderOf_coe]
    have hordx : orderOf xR = orderOf x := Subgroup.orderOf_mk x hxR
    rw [hord] at hle
    rw [hordx] at hlt
    exact absurd hle (not_le.mpr hlt)
  have hRp : IsPGroup 2 R := hS2.to_le hRS
  have : (A.subgroupOf R).Normal := normal_subgroupOf_of_le hRS hAn
  have hAc' : ∀ a ∈ A.subgroupOf R, ∀ b ∈ A.subgroupOf R, a * b = b * a := fun a ha b hb =>
    Subtype.ext (hAc a.1 ha b.1 hb)
  have hA4' : ∀ a ∈ A.subgroupOf R, a ^ 4 = 1 := fun a ha =>
    Subtype.ext (by simpa using hA4 a.1 ha)
  have hgen : (A.subgroupOf R) ⊔ zpowers xR = ⊤ := sup_subgroupOf_zpowers_eq_top A x hxR
  obtain ⟨-, ⟨w, hwA, hwT, hwϕ⟩, c, hcA, hcov⟩ := endgame hRp hAc' hA4' hgen hT hc hd
  refine ⟨h⁻¹, fun hm => hhM (by simpa using M.inv_mem hm), ?_, ?_⟩
  ·
    refine Nat.le_of_dvd two_pos (Subgroup.relIndex_dvd_two_iff.mpr ?_)
    refine ⟨h⁻¹ * ((c : R) : G)⁻¹ * h⁻¹⁻¹, ⟨((c : R) : G)⁻¹, A.inv_mem hcA, by
      simp⟩, ?_⟩
    rintro _ ⟨u, hu, rfl⟩
    have hu' : (⟨u, hAR hu⟩ : R) ∈ A.subgroupOf R := hu
    rcases hcov _ hu' with hT' | hT'
    · right
      have := (mem_stabilizer_coset R h ⟨u, hAR hu⟩).mp hT'
      simpa [MulAut.conj_apply] using this
    · left
      have := (mem_stabilizer_coset R h (⟨u, hAR hu⟩ * c⁻¹)).mp hT'
      have e : (MulAut.conj h⁻¹).toMonoidHom u * (h⁻¹ * ((c : R) : G)⁻¹ * h⁻¹⁻¹) =
          h⁻¹ * (((⟨u, hAR hu⟩ * c⁻¹ : R)) : G) * h := by
        simp; group
      rw [e]; exact this
  ·
    intro hsub
    have hwG : h⁻¹ * (w : G) * h ∈ M := (mem_stabilizer_coset R h w).mp hwT
    have hmem : h⁻¹ * (w : G) * h ∈ A.map (MulAut.conj h⁻¹).toMonoidHom ⊓ M :=
      ⟨⟨(w : G), hwA, by simp⟩, hwG⟩
    have h1 := hsub hmem
    have h3 : μ ⟨h⁻¹ * (w : G) * h, hwG⟩ = 1 := (hμ _).mpr h1
    rw [ext_phiR, ext_of_mem μ hwG] at hwϕ
    exact hwϕ h3

end Main

end CFSG.CGT.PushingUpLit.T211
