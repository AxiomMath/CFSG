module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUStatement

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup
open scoped commutatorElement

section Induced

variable {Y : Type*} [Group Y]

theorem fusionOddCore_map_mulEquiv (σ : MulAut Y) :
    (Open.fusionOddCore Y).map σ.toMonoidHom = Open.fusionOddCore Y := by
  rw [UnbalancingLocal.fusionOddCore_eq_pPrimeCore]
  exact pPrimeCore_map_iso 2 σ

@[expose] noncomputable def zStarAut (Y : Type*) [Group Y] :
    MulAut Y →* MulAut (Y ⧸ Open.fusionZStar Y) where
  toFun σ := QuotientGroup.congr _ _ σ (fusionZStar_map_mulEquiv σ)
  map_one' := by
    ext s
    induction s using QuotientGroup.induction_on
    rfl
  map_mul' σ τ := by
    ext s
    induction s using QuotientGroup.induction_on
    rfl

@[expose] noncomputable def oddAut (Y : Type*) [Group Y] :
    MulAut Y →* MulAut (Y ⧸ Open.fusionOddCore Y) where
  toFun σ := QuotientGroup.congr _ _ σ (fusionOddCore_map_mulEquiv σ)
  map_one' := by
    ext s
    induction s using QuotientGroup.induction_on
    rfl
  map_mul' σ τ := by
    ext s
    induction s using QuotientGroup.induction_on
    rfl

@[simp]
theorem zStarAut_mk (σ : MulAut Y) (y : Y) :
    zStarAut Y σ (QuotientGroup.mk y) = QuotientGroup.mk (σ y) :=
  rfl

@[simp]
theorem oddAut_mk (σ : MulAut Y) (y : Y) :
    oddAut Y σ (QuotientGroup.mk y) = QuotientGroup.mk (σ y) :=
  rfl

theorem mem_fusionZStar_iff (y : Y) :
    y ∈ Open.fusionZStar Y ↔
      (QuotientGroup.mk y : Y ⧸ Open.fusionOddCore Y) ∈ center (Y ⧸ Open.fusionOddCore Y) :=
  Iff.rfl

theorem fusionOddCore_le_fusionZStar : Open.fusionOddCore Y ≤ Open.fusionZStar Y := by
  intro y hy
  rw [mem_fusionZStar_iff, (QuotientGroup.eq_one_iff y).mpr hy]
  exact one_mem _

theorem zStarAut_conj (c : Y) :
    zStarAut Y (MulAut.conj c) = MulAut.conj (QuotientGroup.mk c) := by
  ext s
  induction s using QuotientGroup.induction_on
  simp [MulAut.conj_apply]

theorem mem_oddCore_of_zStarAut_eq_one [Group.IsPerfect Y] {σ : MulAut Y}
    (hσ : zStarAut Y σ = 1) (y : Y) : y⁻¹ * σ y ∈ Open.fusionOddCore Y := by
  set Q := Y ⧸ Open.fusionOddCore Y
  let e : Y → Q := fun x => (QuotientGroup.mk x : Q)⁻¹ * QuotientGroup.mk (σ x)
  have hcen : ∀ x : Y, e x ∈ center Q := fun x => by
    have hx : x⁻¹ * σ x ∈ Open.fusionZStar Y := by
      rw [← QuotientGroup.eq]
      have h := congrArg (fun τ : MulAut (Y ⧸ Open.fusionZStar Y) => τ (QuotientGroup.mk x)) hσ
      simpa using h.symm
    rw [mem_fusionZStar_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv] at hx
    exact hx
  let f : Y →* center Q :=
    { toFun := fun x => ⟨e x, hcen x⟩
      map_one' := by ext; simp [e]
      map_mul' := fun x z => by
        ext
        show e (x * z) = e x * e z
        have hc := mem_center_iff.mp (hcen x)
        calc e (x * z) = (QuotientGroup.mk z : Q)⁻¹ * (e x * QuotientGroup.mk (σ z)) := by
              simp only [e, map_mul, QuotientGroup.mk_mul]
              group
          _ = (QuotientGroup.mk z : Q)⁻¹ * (QuotientGroup.mk (σ z) * e x) := by
              rw [hc (QuotientGroup.mk (σ z))]
          _ = e x * e z := by
              rw [← mul_assoc]
              exact hc _ }
  have hker : commutator Y ≤ f.ker := by
    rw [_root_.commutator_def, commutator_le]
    intro g₁ _ g₂ _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact Subtype.ext (mem_center_iff.mp (f g₂).2 _)
  have h1 : f y = 1 := hker Group.IsPerfect.mem_commutator
  have h2 : e y = 1 := congrArg Subtype.val h1
  have h3 : (QuotientGroup.mk (y⁻¹ * σ y) : Q) = 1 := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    exact h2
  exact (QuotientGroup.eq_one_iff _).mp h3

theorem exists_odd_preimage [Finite Y] (N : Subgroup Y) [N.Normal] {s : Y ⧸ N}
    (hs : Odd (orderOf s)) : ∃ y : Y, (QuotientGroup.mk y : Y ⧸ N) = s ∧ Odd (orderOf y) := by
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective s
  obtain ⟨e, r, hr, hyr⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y).ne'
  set m := orderOf (QuotientGroup.mk y : Y ⧸ N) with hm
  have hcop : Nat.Coprime (2 ^ e) m := Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hs)
  have hφ : 0 < Nat.totient m := Nat.totient_pos.mpr (orderOf_pos _)
  refine ⟨y ^ ((2 ^ e) ^ Nat.totient m), ?_, ?_⟩
  · rw [QuotientGroup.mk_pow]
    conv_rhs => rw [← pow_one (QuotientGroup.mk y : Y ⧸ N)]
    exact pow_eq_pow_iff_modEq.mpr (Nat.ModEq.pow_totient hcop)
  · have hdvd : orderOf y ∣ (2 ^ e) ^ Nat.totient m * r := by
      rw [hyr]
      exact Nat.mul_dvd_mul_right (dvd_pow_self _ hφ.ne') r
    have h1 : (y ^ ((2 ^ e) ^ Nat.totient m)) ^ r = 1 := by
      rw [← pow_mul]
      exact orderOf_dvd_iff_pow_eq_one.mp hdvd
    exact Odd.of_dvd_nat hr (orderOf_dvd_of_pow_eq_one h1)

theorem exists_fixed_lift [Finite Y] {α : MulAut Y} (hα : ∀ y, α (α y) = y)
    {s : Y ⧸ Open.fusionZStar Y} (hs : Odd (orderOf s)) (hsα : zStarAut Y α s = s) :
    ∃ c : Y, α c = c ∧ (QuotientGroup.mk c : Y ⧸ Open.fusionZStar Y) = s := by
  classical
  obtain ⟨y₀, rfl, hodd⟩ := exists_odd_preimage _ hs
  set O := Open.fusionOddCore Y with hO
  set u : Y ⧸ O := QuotientGroup.mk y₀
  set z : Y ⧸ O := u⁻¹ * QuotientGroup.mk (α y₀) with hzdef
  have hz : z ∈ center (Y ⧸ O) := by
    have h : y₀⁻¹ * α y₀ ∈ Open.fusionZStar Y := by
      rw [← QuotientGroup.eq]
      exact hsα.symm
    rw [mem_fusionZStar_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h
    exact h
  have hzc := mem_center_iff.mp hz
  have huz : (QuotientGroup.mk (α y₀) : Y ⧸ O) = u * z := by rw [hzdef]; group
  set m := orderOf y₀ with hm
  have hzm : z ^ m = 1 := by
    have h1 : u ^ m = 1 := by rw [← QuotientGroup.mk_pow, pow_orderOf_eq_one]; rfl
    have h2 : (QuotientGroup.mk (α y₀) : Y ⧸ O) ^ m = 1 := by
      rw [← QuotientGroup.mk_pow, ← map_pow, pow_orderOf_eq_one, map_one]; rfl
    rw [huz, (show Commute u z from hzc u).mul_pow, h1, one_mul] at h2
    exact h2
  have hαz : oddAut Y α z = z⁻¹ := by
    rw [hzdef, map_mul, map_inv, oddAut_mk, oddAut_mk, hα, huz,
      show (QuotientGroup.mk y₀ : Y ⧸ O) = u from rfl]
    group
  set k := (m + 1) / 2 with hk
  have h2k : 2 * k = m + 1 := by
    have := Nat.odd_iff.mp hodd
    omega
  obtain ⟨t, ht⟩ := QuotientGroup.mk_surjective (z ^ k)
  have htZ : t ∈ Open.fusionZStar Y := by
    rw [mem_fusionZStar_iff, ht]
    exact pow_mem hz k
  set v := y₀ * t with hv
  have hdO : v⁻¹ * α v ∈ O := by
    rw [← QuotientGroup.eq_one_iff]
    have hαt : (QuotientGroup.mk (α t) : Y ⧸ O) = (z ^ k)⁻¹ := by
      rw [← oddAut_mk, ht, map_pow, hαz, inv_pow]
    have hzk : z * ((z ^ k)⁻¹ * (z ^ k)⁻¹) = 1 := by
      rw [← mul_inv_rev, ← pow_add, ← two_mul, h2k, pow_succ, hzm, one_mul, mul_inv_cancel]
    calc (QuotientGroup.mk (v⁻¹ * α v) : Y ⧸ O)
        = (u * z ^ k)⁻¹ * ((u * z) * (z ^ k)⁻¹) := by
          rw [hv, map_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_mul,
            QuotientGroup.mk_mul, ht, huz, hαt]
      _ = (z ^ k)⁻¹ * z * (z ^ k)⁻¹ := by group
      _ = 1 := by
          rw [hzc ((z ^ k)⁻¹), mul_assoc]
          exact hzk
  set d := v⁻¹ * α v
  have hαO : ∀ o ∈ O, α o ∈ O := fun o ho => by
    have h := fusionOddCore_map_mulEquiv α
    rw [← hO] at h
    rw [← h]
    exact mem_map_of_mem _ ho
  let f : O → O := fun o => ⟨d * α o, mul_mem hdO (hαO o o.2)⟩
  have hd : d * α d = 1 := by
    simp only [d, map_mul, map_inv, hα]
    group
  have hff : ∀ o, f (f o) = o := fun o => by
    apply Subtype.ext
    show d * α (d * α o) = o
    rw [map_mul, hα, ← mul_assoc, hd, one_mul]
  have : Fintype O := Fintype.ofFinite O
  let σ : Equiv.Perm O := ⟨f, f, hff, hff⟩
  have hσ : σ ^ 2 ^ 1 = 1 := by
    ext o
    simp only [pow_one, sq, Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
    exact congrArg Subtype.val (hff o)
  have hcard : ¬ 2 ∣ Fintype.card O := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hc := pPrimeCore_coprime_card (p := 2) (G := Y)
    rw [← UnbalancingLocal.fusionOddCore_eq_pPrimeCore, Nat.card_eq_fintype_card] at hc
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1 hc
  obtain ⟨o₀, ho₀⟩ := Equiv.Perm.exists_fixed_point_of_prime (p := 2) hcard hσ
  have ho₀' : d * α o₀ = o₀ := congrArg Subtype.val ho₀
  refine ⟨v * o₀, ?_, ?_⟩
  · rw [map_mul]
    calc α v * α o₀ = v * (d * α o₀) := by simp only [d]; group
      _ = v * o₀ := by rw [ho₀']
  · rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff (o₀ : Y)).mpr
      (fusionOddCore_le_fusionZStar o₀.2), mul_one, hv, QuotientGroup.mk_mul,
      (QuotientGroup.eq_one_iff t).mpr htZ, mul_one]

theorem mulAut_conj_map {S : Type*} [Group S] (σ : MulAut S) (s : S) :
    MulAut.conj (σ s) = σ * MulAut.conj s * σ⁻¹ := by
  ext x
  simp only [MulAut.conj_apply, MulAut.mul_apply, map_mul, map_inv, MulAut.apply_inv_self]

theorem mulAut_conj_injective {S : Type*} [Group S] (hZ : center S = ⊥) :
    Function.Injective (MulAut.conj : S →* MulAut S) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro s hs
  rw [← hZ]
  refine mem_center_iff.mpr fun x => ?_
  have h := congrArg (fun τ : MulAut S => τ x) (MonoidHom.mem_ker.mp hs)
  simp only [MulAut.conj_apply, MulAut.one_apply] at h
  calc x * s = s * x * s⁻¹ * s := by rw [h]
    _ = s * x := by group

theorem map_le_oddCore_centralizer [Finite Y] [IsSimpleGroup (Y ⧸ Open.fusionZStar Y)]
    (hna : ∃ a b : Y ⧸ Open.fusionZStar Y, a * b ≠ b * a) {α : MulAut Y}
    (hα : ∀ y, α (α y) = y) (A : Subgroup (MulAut Y)) (hAodd : Odd (Nat.card A))
    (h1 : ∀ β ∈ A, β * α = α * β)
    (h2 : ∀ c : Y, α c = c → ∀ β ∈ A, MulAut.conj c * β * (MulAut.conj c)⁻¹ ∈ A)
    (h3 : ∀ β ∈ A, ∃ s : Y ⧸ Open.fusionZStar Y, zStarAut Y β = MulAut.conj s) :
    A.map (zStarAut Y) ≤ (pPrimeCore 2 ↥(centralizer ({zStarAut Y α} : Set
      (MulAut (Y ⧸ Open.fusionZStar Y))))).map (centralizer ({zStarAut Y α} : Set
      (MulAut (Y ⧸ Open.fusionZStar Y)))).subtype := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S := Y ⧸ Open.fusionZStar Y
  set ᾱ := zStarAut Y α with hᾱ
  set B := A.map (zStarAut Y) with hB
  set Q := centralizer ({ᾱ} : Set (MulAut S)) with hQ
  have hZ : center S = ⊥ := center_eq_bot_of_isSimpleGroup hna
  have hκ := mulAut_conj_injective hZ
  set gens : Set S := {s | ᾱ s = s ∧ Odd (orderOf s)} with hgens
  set T : Subgroup S := closure gens with hT
  set X : Subgroup (MulAut S) := T.map MulAut.conj with hX
  have hBgen : ∀ β ∈ A, ∃ s ∈ gens, zStarAut Y β = MulAut.conj s := by
    intro β hβ
    obtain ⟨s, hs⟩ := h3 β hβ
    refine ⟨s, ⟨?_, ?_⟩, hs⟩
    · apply hκ
      have hc : zStarAut Y (β * α) = zStarAut Y (α * β) := congrArg _ (h1 β hβ)
      rw [map_mul, map_mul, hs] at hc
      rw [mulAut_conj_map, ← hc, mul_inv_cancel_right]
    · have hodd : Odd (orderOf β) := by
        have h := orderOf_dvd_natCard (⟨β, hβ⟩ : A)
        rw [Subgroup.orderOf_mk] at h
        exact Odd.of_dvd_nat hAodd h
      have hd : orderOf (zStarAut Y β) ∣ orderOf β := orderOf_map_dvd _ _
      rw [hs, orderOf_injective _ hκ] at hd
      exact Odd.of_dvd_nat hodd hd
  have hBX : B ≤ X := by
    rintro _ ⟨β, hβ, rfl⟩
    obtain ⟨s, hs, hβs⟩ := hBgen β hβ
    exact ⟨s, subset_closure hs, hβs.symm⟩
  have hXQ : X ≤ Q := by
    rw [hX, hT, MonoidHom.map_closure, closure_le]
    rintro _ ⟨s, hs, rfl⟩
    rw [SetLike.mem_coe, hQ, mem_centralizer_singleton_iff]
    have h := mulAut_conj_map ᾱ s
    rw [hs.1] at h
    calc MulAut.conj s * ᾱ = ᾱ * MulAut.conj s * ᾱ⁻¹ * ᾱ := by rw [← h]
      _ = ᾱ * MulAut.conj s := by group
  have hTinv : ∀ γ ∈ Q, ∀ t ∈ T, γ t ∈ T := by
    intro γ hγ t ht
    have hγα : γ * ᾱ = ᾱ * γ := mem_centralizer_singleton_iff.mp hγ
    have hsub : T ≤ T.comap γ.toMonoidHom := by
      rw [hT, closure_le]
      intro s hs
      refine subset_closure ⟨?_, ?_⟩
      · have h := congrArg (fun τ : MulAut S => τ s) hγα
        simp only [MulAut.mul_apply] at h
        show ᾱ (γ s) = γ s
        rw [← h, hs.1]
      · rw [orderOf_injective γ.toMonoidHom γ.injective s]
        exact hs.2
    exact hsub ht
  have hQN : Q ≤ normalizer (X : Set (MulAut S)) := by
    have key : ∀ γ ∈ Q, ∀ x ∈ X, γ * x * γ⁻¹ ∈ X := by
      rintro γ hγ _ ⟨t, ht, rfl⟩
      exact ⟨γ t, hTinv γ hγ t ht, mulAut_conj_map γ t⟩
    intro γ hγ
    refine mem_normalizer_iff.mpr fun x => ⟨key γ hγ x, fun hx => ?_⟩
    have := key γ⁻¹ (inv_mem hγ) _ hx
    rwa [inv_inv, show γ⁻¹ * (γ * x * γ⁻¹) * γ = x by group] at this
  have hconjB : ∀ s ∈ gens, ∀ b ∈ B, MulAut.conj s * b * (MulAut.conj s)⁻¹ ∈ B := by
    rintro s hs _ ⟨β, hβ, rfl⟩
    obtain ⟨c, hc, rfl⟩ := exists_fixed_lift hα hs.2 hs.1
    refine ⟨MulAut.conj c * β * (MulAut.conj c)⁻¹, h2 c hc β hβ, ?_⟩
    simp only [map_mul, map_inv, zStarAut_conj]
  have hXN : X ≤ normalizer (B : Set (MulAut S)) := by
    rw [hX, hT, MonoidHom.map_closure, closure_le]
    rintro _ ⟨s, hs, rfl⟩
    refine mem_normalizer_iff.mpr fun b => ⟨hconjB s hs b, fun hb => ?_⟩
    have hs' : s⁻¹ ∈ gens := ⟨by rw [map_inv, hs.1], by rw [orderOf_inv]; exact hs.2⟩
    have := hconjB s⁻¹ hs' _ hb
    rwa [map_inv, inv_inv, show (MulAut.conj s)⁻¹ * (MulAut.conj s * b * (MulAut.conj s)⁻¹) *
      MulAut.conj s = b by group] at this
  have hBodd : Nat.Coprime 2 (Nat.card B) :=
    Nat.coprime_two_left.mpr (Odd.of_dvd_nat hAodd (card_map_dvd A _))
  have hBO : B.subgroupOf X ≤ pPrimeCore 2 ↥X := by
    apply le_sSup
    refine ⟨(normal_subgroupOf_iff hBX).mpr fun b x hb hx => ?_, ?_⟩
    · have := (mem_normalizer_iff.mp (hXN hx) b).mp hb
      exact this
    · rw [Nat.card_congr (subgroupOfEquivOfLe hBX).toEquiv]
      exact hBodd
  set P := (pPrimeCore 2 ↥X).map X.subtype with hP
  have hBP : B ≤ P := by
    intro b hb
    exact ⟨⟨b, hBX hb⟩, hBO (mem_subgroupOf.mpr hb), rfl⟩
  have hPQ : P ≤ Q := (map_subtype_le _).trans hXQ
  have hPO : P.subgroupOf Q ≤ pPrimeCore 2 ↥Q := by
    apply le_sSup
    refine ⟨(normal_subgroupOf_iff hPQ).mpr fun x γ hx hγ => ?_, ?_⟩
    · exact Walter.conj_mem_map_of_characteristic (hQN hγ) hx
    · rw [Nat.card_congr (subgroupOfEquivOfLe hPQ).toEquiv, hP,
        card_map_of_injective (subtype_injective _)]
      exact pPrimeCore_coprime_card
  intro b hb
  exact ⟨⟨b, hPQ (hBP hb)⟩, hPO (mem_subgroupOf.mpr (hBP hb)), rfl⟩

end Induced

@[expose] def FooteLBalanceInput : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (a : H), orderOf a = 2 → ∀ L : Subgroup H,
    IsPComponent 2 L → oddCoreOfCentralizer a ≤ normalizer (L : Set H) ∧
      ((conjugate L a ≠ L ∨ ∀ x ∈ L, x⁻¹ * a⁻¹ * x * a ∈ (pPrimeCore 2 L).map L.subtype) →
        ⁅oddCoreOfCentralizer a, L⁆ ≤ (pPrimeCore 2 L).map L.subtype)

@[expose] def OddOuterInner (S : Type*) [Group S] : Prop :=
  ∀ σ : MulAut S, Odd (orderOf σ) → ∃ s : S, σ = MulAut.conj s

theorem zStarQuotient_simple {K : Type*} [Group K] [Finite K] {Y : Subgroup K}
    (hY : IsPComponent 2 Y) :
    IsSimpleGroup (Y ⧸ Open.fusionZStar Y) ∧ ∃ a b : Y ⧸ Open.fusionZStar Y, a * b ≠ b * a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq := CatalogueBHeldSmallCore.pComponent_coreQuotient_quasisimple 2 Y hY
  set O := Open.fusionOddCore ↥Y
  have hq₁ : IsQuasisimple (↥Y ⧸ O) := LocalCores.isQuasisimple_of_mulEquiv
    (QuotientGroup.quotientMulEquivOfEq (UnbalancingLocal.fusionOddCore_eq_pPrimeCore ↥Y)).symm hq
  have hmap : (Open.fusionZStar ↥Y).map (QuotientGroup.mk' O) = center (↥Y ⧸ O) :=
    map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective O) _
  let e : (↥Y ⧸ O) ⧸ center (↥Y ⧸ O) ≃* ↥Y ⧸ Open.fusionZStar ↥Y :=
    (QuotientGroup.quotientMulEquivOfEq hmap.symm).trans
      (QuotientGroup.quotientQuotientEquivQuotient O (Open.fusionZStar ↥Y)
        fusionOddCore_le_fusionZStar)
  obtain ⟨-, hs, a, b, hab⟩ := hq₁
  refine ⟨e.symm.isSimpleGroup, e a, e b, fun h => hab (e.injective ?_)⟩
  rw [map_mul, map_mul]
  exact h

section Main

variable {K : Type} [Group K] [Finite K]

omit [Finite K] in
theorem normalizerMonoidHom_of_mem {Y : Subgroup K} {c : K} (hc : c ∈ Y) :
    Y.normalizerMonoidHom ⟨c, le_normalizer hc⟩ = MulAut.conj ⟨c, hc⟩ := by
  ext y
  simp [MulAut.conj_apply]

theorem commutator_mem_oddCore_of_zStarAut_eq_one {Y : Subgroup K} (hY : IsPComponent 2 Y)
    {g : K} (hg : g ∈ normalizer (Y : Set K)) (h1 : zStarAut Y (Y.normalizerMonoidHom ⟨g, hg⟩) = 1)
    {y : K} (hy : y ∈ Y) : ⁅g, y⁆ ∈ (pPrimeCore 2 Y).map Y.subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsPerfect Y := CatalogueBHeldSmallCore.pComponent_perfect 2 Y hY
  have hm := mem_oddCore_of_zStarAut_eq_one h1 ⟨y, hy⟩
  rw [UnbalancingLocal.fusionOddCore_eq_pPrimeCore] at hm
  have hm' : y⁻¹ * (g * y * g⁻¹) ∈ (pPrimeCore 2 Y).map Y.subtype :=
    ⟨_, hm, by simp⟩
  have hconj := Walter.conj_mem_map_of_characteristic (D := pPrimeCore 2 ↥Y)
    (le_normalizer hy) hm'
  rw [show y * (y⁻¹ * (g * y * g⁻¹)) * y⁻¹ = ⁅g, y⁆ by rw [commutatorElement_def]; group]
    at hconj
  exact hconj

theorem zStarAut_mem_oddCore_centralizer {Y : Subgroup K} (hY : IsPComponent 2 Y) {a : K}
    (ha : orderOf a = 2) (haN : a ∈ normalizer (Y : Set K))
    (hWN : oddCoreOfCentralizer a ≤ normalizer (Y : Set K))
    (hout : OddOuterInner (Y ⧸ Open.fusionZStar Y)) {w : K} (hw : w ∈ oddCoreOfCentralizer a) :
    zStarAut Y (Y.normalizerMonoidHom ⟨w, hWN hw⟩) ∈
      (pPrimeCore 2 ↥(centralizer ({zStarAut Y (Y.normalizerMonoidHom ⟨a, haN⟩)} :
        Set (MulAut (Y ⧸ Open.fusionZStar Y))))).map (centralizer
        ({zStarAut Y (Y.normalizerMonoidHom ⟨a, haN⟩)} :
          Set (MulAut (Y ⧸ Open.fusionZStar Y)))).subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hsimple, hna⟩ := zStarQuotient_simple hY
  set N := normalizer (Y : Set K)
  set ψ := Y.normalizerMonoidHom
  set W := oddCoreOfCentralizer a
  set α := ψ ⟨a, haN⟩ with hαdef
  have ha2 : a * a = 1 := by rw [← sq, ← ha]; exact pow_orderOf_eq_one a
  have hα : ∀ y, α (α y) = y := fun y => by
    rw [← MulAut.mul_apply, hαdef, ← map_mul]
    have : (⟨a, haN⟩ : N) * ⟨a, haN⟩ = 1 := Subtype.ext ha2
    rw [this, map_one, MulAut.one_apply]
  set A := (W.subgroupOf N).map ψ with hA
  have hWodd : Odd (Nat.card W) := by
    have h : Nat.card W = Nat.card (pPrimeCore 2 ↥(centralizer ({a} : Set K))) :=
      card_map_of_injective (subtype_injective _)
    rw [h]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hAodd : Odd (Nat.card A) := by
    refine Odd.of_dvd_nat ?_ (card_map_dvd _ _)
    rwa [Nat.card_congr (subgroupOfEquivOfLe hWN).toEquiv]
  have hWa : ∀ w ∈ W, w * a = a * w := fun w hw =>
    mem_centralizer_singleton_iff.mp (oddCoreOfCentralizer_le_centralizer a hw)
  have h1 : ∀ β ∈ A, β * α = α * β := by
    rintro _ ⟨⟨w, hwN⟩, hw, rfl⟩
    rw [hαdef, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hWa w (mem_subgroupOf.mp hw))
  have h2 : ∀ c : Y, α c = c → ∀ β ∈ A, MulAut.conj c * β * (MulAut.conj c)⁻¹ ∈ A := by
    rintro c hc _ ⟨⟨w, hwN⟩, hw, rfl⟩
    have hcC : (c : K) ∈ centralizer ({a} : Set K) := by
      have h := congrArg Subtype.val hc
      rw [hαdef, normalizerMonoidHom_apply_apply_coe] at h
      apply mem_centralizer_singleton_iff.mpr
      calc (c : K) * a = a * c * a⁻¹ * a := by rw [h]
        _ = a * c := by group
    have hcw : (c : K) * w * (c : K)⁻¹ ∈ W :=
      conj_mem_oddCoreOfCentralizer hcC (mem_subgroupOf.mp hw)
    refine ⟨⟨(c : K), le_normalizer c.2⟩ * ⟨w, hwN⟩ * ⟨(c : K), le_normalizer c.2⟩⁻¹,
      mem_subgroupOf.mpr hcw, ?_⟩
    rw [map_mul, map_mul, map_inv, normalizerMonoidHom_of_mem c.2]
  have h3 : ∀ β ∈ A, ∃ s : Y ⧸ Open.fusionZStar Y, zStarAut Y β = MulAut.conj s := by
    intro β hβ
    refine hout _ (Odd.of_dvd_nat ?_ (orderOf_map_dvd _ _))
    have h := orderOf_dvd_natCard (⟨β, hβ⟩ : A)
    rw [Subgroup.orderOf_mk] at h
    exact Odd.of_dvd_nat hAodd h
  exact map_le_oddCore_centralizer hna hα A hAodd h1 h2 h3
    ⟨ψ ⟨w, hWN hw⟩, ⟨⟨w, hWN hw⟩, mem_subgroupOf.mpr hw, rfl⟩, rfl⟩

omit [Finite K] in
theorem mem_normalizer_of_conjugate_eq {Y : Subgroup K} {g : K} (h : conjugate Y g = Y) :
    g ∈ normalizer (Y : Set K) := by
  have hmem : ∀ x, x ∈ conjugate Y g ↔ g * x * g⁻¹ ∈ Y := fun x => by
    constructor
    · rintro ⟨y, hy, rfl⟩
      show g * ((MulAut.conj g⁻¹) y) * g⁻¹ ∈ Y
      rw [MulAut.conj_apply, show g * (g⁻¹ * y * g⁻¹⁻¹) * g⁻¹ = y by group]
      exact hy
    · intro hx
      refine ⟨g * x * g⁻¹, hx, ?_⟩
      show (MulAut.conj g⁻¹) (g * x * g⁻¹) = x
      rw [MulAut.conj_apply]
      group
  exact mem_normalizer_iff.mpr fun x =>
    ⟨fun hx => (hmem x).mp (h.symm ▸ hx), fun hx => h ▸ (hmem x).mpr hx⟩

omit [Finite K] in
theorem commutator_self_le (W : Subgroup K) : ⁅W, W⁆ ≤ W := by
  rw [commutator_le]
  intro g₁ h₁ g₂ h₂
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem h₁ h₂) (inv_mem h₁)) (inv_mem h₂)

theorem footeCore_of_abelianCore_of_oddOuterInner (hLB : FooteLBalanceInput)
    (hAC : FooteAbelianCoreAxiom) (hK : SectionRank.IsKGroupCat K) {a : K} (ha : orderOf a = 2)
    {Y : Subgroup K} (hY : IsPComponent 2 Y) (hout : OddOuterInner (Y ⧸ Open.fusionZStar Y)) :
    (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
      Blueprint.LieModel (Y ⧸ Open.fusionZStar Y) .PSL 2 p f) ∨
    ⁅⁅oddCoreOfCentralizer a, oddCoreOfCentralizer a⁆, Y⁆ ≤ pPrimeCore 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hL2 : ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
      Blueprint.LieModel (Y ⧸ Open.fusionZStar Y) .PSL 2 p f
  · exact Or.inl hL2
  right
  have hsub : Y.IsSubnormal := by
    obtain ⟨-, -, h, -, -⟩ := hY
    exact h
  have hOK := Walter.map_pPrimeCore_le_of_isSubnormal hsub
  obtain ⟨hWN, hcent⟩ := hLB K a ha Y hY
  set W := oddCoreOfCentralizer a
  have hWW := commutator_self_le W
  by_cases hswap : conjugate Y a ≠ Y
  · exact ((commutator_mono hWW le_rfl).trans (hcent (Or.inl hswap))).trans hOK
  have haN := mem_normalizer_of_conjugate_eq (not_not.mp hswap)
  set ψ := Y.normalizerMonoidHom
  set ᾱ := zStarAut Y (ψ ⟨a, haN⟩) with hᾱ
  have ha2 : a * a = 1 := by rw [← sq, ← ha]; exact pow_orderOf_eq_one a
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  by_cases hα1 : ᾱ = 1
  ·
    refine ((commutator_mono hWW le_rfl).trans (hcent (Or.inr fun x hx => ?_))).trans hOK
    have hc := commutator_mem_oddCore_of_zStarAut_eq_one hY haN hα1 hx
    have hc' := Walter.conj_mem_map_of_characteristic (D := pPrimeCore 2 ↥Y)
      (le_normalizer (inv_mem hx)) hc
    rw [show x⁻¹ * ⁅a, x⁆ * x⁻¹⁻¹ = x⁻¹ * a⁻¹ * x * a by
      rw [commutatorElement_def, hainv]; group] at hc'
    exact hc'
  obtain ⟨hsimple, hna⟩ := zStarQuotient_simple hY
  have hord : orderOf ᾱ = 2 := by
    refine orderOf_eq_prime ?_ hα1
    rw [hᾱ, ← map_pow, ← map_pow, sq]
    have : (⟨a, haN⟩ : normalizer (Y : Set K)) * ⟨a, haN⟩ = 1 := Subtype.ext ha2
    rw [this, map_one, map_one]
  have hcomm := hAC _ hna (hK Y (Open.fusionZStar Y) hsimple) hL2 ᾱ hord
  have hker : ⁅W, W⁆ ≤ ((zStarAut Y).comp ψ).ker.map (normalizer (Y : Set K)).subtype := by
    rw [commutator_le]
    intro w₁ hw₁ w₂ hw₂
    refine ⟨⁅(⟨w₁, hWN hw₁⟩ : normalizer (Y : Set K)), ⟨w₂, hWN hw₂⟩⁆, ?_,
      by simp [commutatorElement_def]⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]
    obtain ⟨x₁, hx₁, e₁⟩ := zStarAut_mem_oddCore_centralizer hY ha haN hWN hout hw₁
    obtain ⟨x₂, hx₂, e₂⟩ := zStarAut_mem_oddCore_centralizer hY ha haN hWN hout hw₂
    show zStarAut Y (ψ ⟨w₁, hWN hw₁⟩) * zStarAut Y (ψ ⟨w₂, hWN hw₂⟩) =
      zStarAut Y (ψ ⟨w₂, hWN hw₂⟩) * zStarAut Y (ψ ⟨w₁, hWN hw₁⟩)
    rw [← e₁, ← e₂]
    have h₁ := hcomm ⟨x₁, hx₁⟩ ⟨x₂, hx₂⟩
    have h₂ : x₁ * x₂ = x₂ * x₁ := by
      have := congrArg Subtype.val h₁
      simpa using this
    have h₃ := congrArg Subtype.val h₂
    simpa using h₃
  rw [commutator_le]
  intro g hg y hy
  obtain ⟨n, hn, rfl⟩ := hker hg
  exact hOK (commutator_mem_oddCore_of_zStarAut_eq_one hY n.2 (by simpa using hn) hy)

@[expose] def UBalanced (S : Type) [Group S] : Prop :=
  ¬ (Blueprint.OddLieType S ∨
    (∃ n : ℕ, Odd n ∧ 7 ≤ n ∧ Nonempty (S ≃* alternatingGroup (Fin n))) ∨
    Blueprint.LieModel S .PSL 3 2 2 ∨ Nonempty (S ≃* Blueprint.NativeSporadic.He))

theorem generalizedFitting_mulAut_eq_range {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hna : ∃ a b : S, a * b ≠ b * a) :
    GeneralizedFitting.subgroup (MulAut S) = (MulAut.conj : S →* MulAut S).range := by
  have hZ : center S = ⊥ := center_eq_bot_of_isSimpleGroup hna
  have hκ := mulAut_conj_injective hZ
  set Inn := (MulAut.conj : S →* MulAut S).range with hInn
  let e : S ≃* Inn := MonoidHom.ofInjective hκ
  have : Inn.Normal := ⟨fun n hn g => by
    obtain ⟨s, rfl⟩ := hn
    exact ⟨g s, mulAut_conj_map g s⟩⟩
  have : IsSimpleGroup Inn := e.symm.isSimpleGroup
  have hnc : ∃ x y : Inn, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hna
    exact ⟨e x, e y, fun h => hxy (e.injective (by rw [map_mul, map_mul]; exact h))⟩
  have hC : centralizer (Inn : Set (MulAut S)) = ⊥ := by
    rw [eq_bot_iff]
    intro σ hσ
    rw [mem_bot]
    ext s
    have h := mem_centralizer_iff.mp hσ (MulAut.conj s) ⟨s, rfl⟩
    have h' : MulAut.conj (σ s) = MulAut.conj s := by
      rw [mulAut_conj_map, ← h, mul_inv_cancel_right]
    exact hκ h'
  rw [← generalizedFitting_eq_componentClassification]
  exact Semidihedral.CoreFreeDihedral.generalizedFitting_eq_of_normal_simple_centralizer_eq_bot
    Inn hnc hC

theorem oddCore_centralizer_mulAut_eq_bot (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome)
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (hna : ∃ a b : S, a * b ≠ b * a)
    (hcat : Blueprint.Catalog S) (hbal : UBalanced S) {i : MulAut S} (hi : orderOf i = 2) :
    pPrimeCore 2 ↥(centralizer ({i} : Set (MulAut S))) = ⊥ := by
  by_contra hne
  have hZ : center S = ⊥ := center_eq_bot_of_isSimpleGroup hna
  have hκ := mulAut_conj_injective hZ
  set Inn := (MulAut.conj : S →* MulAut S).range with hInn
  let e : S ≃* Inn := MonoidHom.ofInjective hκ
  have hF := generalizedFitting_mulAut_eq_range hna
  have : IsSimpleGroup Inn := e.symm.isSimpleGroup
  have hs : IsSimpleGroup (GeneralizedFitting.subgroup (MulAut S)) := by
    rw [hF]
    infer_instance
  have hnc : ∃ x y : GeneralizedFitting.subgroup (MulAut S), x * y ≠ y * x := by
    rw [hF]
    obtain ⟨x, y, hxy⟩ := hna
    exact ⟨e x, e y, fun h => hxy (e.injective (by rw [map_mul, map_mul]; exact h))⟩
  have hc : Blueprint.Catalog (GeneralizedFitting.subgroup (MulAut S)) := by
    rw [hF]
    exact SectionRank.catalog_of_mulEquiv e.symm hcat
  have hz : ∃ z : MulAut S, orderOf z = 2 ∧
      CFSG.oddCore (centralizer ({z} : Set (MulAut S))) ≠ ⊥ :=
    ⟨i, hi, by rwa [oddCore_eq_pPrimeCore_two]⟩
  have hout := hU (MulAut S) hs hnc hc hz
  unfold OutcomeLocal.UOutcome at hout
  rw [hF] at hout
  apply hbal
  rcases hout with h | ⟨n, hn, h7, ⟨e'⟩, -⟩ | ⟨h | ⟨⟨e'⟩⟩, -⟩
  · exact Or.inl ((ClassicalInvolution.oddLieType_congr e).2 h)
  · exact Or.inr (Or.inl ⟨n, hn, h7, ⟨e.trans e'⟩⟩)
  · exact Or.inr (Or.inr (Or.inl (LieType.CurtisTits.lieModel_of_mulEquiv e.symm h)))
  · exact Or.inr (Or.inr (Or.inr ⟨e.trans e'⟩))

theorem core_commutator_le_of_balanced_of_oddOuterInner (hLB : FooteLBalanceInput)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hK : SectionRank.IsKGroupCat K)
    {a : K} (ha : orderOf a = 2) {Y : Subgroup K} (hY : IsPComponent 2 Y)
    (hout : OddOuterInner (Y ⧸ Open.fusionZStar Y)) (hbal : UBalanced (Y ⧸ Open.fusionZStar Y)) :
    ⁅oddCoreOfCentralizer a, Y⁆ ≤ pPrimeCore 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsub : Y.IsSubnormal := by
    obtain ⟨-, -, h, -, -⟩ := hY
    exact h
  have hOK := Walter.map_pPrimeCore_le_of_isSubnormal hsub
  obtain ⟨hWN, hcent⟩ := hLB K a ha Y hY
  set W := oddCoreOfCentralizer a
  by_cases hswap : conjugate Y a ≠ Y
  · exact (hcent (Or.inl hswap)).trans hOK
  have haN := mem_normalizer_of_conjugate_eq (not_not.mp hswap)
  set ψ := Y.normalizerMonoidHom
  set ᾱ := zStarAut Y (ψ ⟨a, haN⟩) with hᾱ
  have ha2 : a * a = 1 := by rw [← sq, ← ha]; exact pow_orderOf_eq_one a
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  by_cases hα1 : ᾱ = 1
  · refine (hcent (Or.inr fun x hx => ?_)).trans hOK
    have hc := commutator_mem_oddCore_of_zStarAut_eq_one hY haN hα1 hx
    have hc' := Walter.conj_mem_map_of_characteristic (D := pPrimeCore 2 ↥Y)
      (le_normalizer (inv_mem hx)) hc
    rw [show x⁻¹ * ⁅a, x⁆ * x⁻¹⁻¹ = x⁻¹ * a⁻¹ * x * a by
      rw [commutatorElement_def, hainv]; group] at hc'
    exact hc'
  obtain ⟨hsimple, hna⟩ := zStarQuotient_simple hY
  have hord : orderOf ᾱ = 2 := by
    refine orderOf_eq_prime ?_ hα1
    rw [hᾱ, ← map_pow, ← map_pow, sq]
    have : (⟨a, haN⟩ : normalizer (Y : Set K)) * ⟨a, haN⟩ = 1 := Subtype.ext ha2
    rw [this, map_one, map_one]
  have hbot := oddCore_centralizer_mulAut_eq_bot hU hna (hK Y (Open.fusionZStar Y) hsimple)
    hbal hord
  rw [commutator_le]
  intro w hw y hy
  refine hOK (commutator_mem_oddCore_of_zStarAut_eq_one hY (hWN hw) ?_ hy)
  obtain ⟨x, hx, ex⟩ := zStarAut_mem_oddCore_centralizer hY ha haN hWN hout hw
  rw [hbot, SetLike.mem_coe, mem_bot] at hx
  rw [← ex, hx]
  rfl

end Main

end CFSG.ComponentClassification.FooteLit
