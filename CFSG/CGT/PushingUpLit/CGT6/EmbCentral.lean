module

public import CFSG.CGT.PushingUpLit.CGT6.EmbDictXfer

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit
open scoped commutatorElement

section Central

variable {L L' : Type} [Group L] [Group L']

structure TwoQuot (Θ : L →* L') : Prop where
  surj : Function.Surjective Θ
  two : IsPGroup 2 ↥Θ.ker

structure CentralTwoQuot (Θ : L →* L') : Prop extends TwoQuot Θ where
  central : Θ.ker ≤ Subgroup.center L

variable {Θ : L →* L'}

theorem TwoQuot.pCore_eq (h : TwoQuot Θ) : pCore 2 L = (pCore 2 L').comap Θ := by
  apply le_antisymm
  · have hn : ((pCore 2 L).map Θ).Normal := (pCore_normal (p := 2) (G := L)).map _ h.surj
    have hp : IsPGroup 2 ↥((pCore 2 L).map Θ) := (pCore_isPGroup (p := 2) (G := L)).map _
    have hle : (pCore 2 L).map Θ ≤ pCore 2 L' := le_sSup ⟨hn, hp⟩
    intro x hx
    exact hle ⟨x, hx, rfl⟩
  · have hn : ((pCore 2 L').comap Θ).Normal := Subgroup.normal_comap _
    have hp : IsPGroup 2 ↥((pCore 2 L').comap Θ) :=
      IsPGroup.comap_of_ker_isPGroup (pCore_isPGroup (p := 2) (G := L')) Θ h.two
    exact le_sSup ⟨hn, hp⟩

theorem TwoQuot.map_pCore (h : TwoQuot Θ) : (pCore 2 L).map Θ = pCore 2 L' := by
  rw [h.pCore_eq, Subgroup.map_comap_eq_self_of_surjective h.surj]

theorem TwoQuot.map_shortU (h : TwoQuot Θ) : (shortU L).map Θ = shortU L' := by
  unfold shortU
  rw [Subgroup.map_commutator, h.map_pCore, Subgroup.map_top, MonoidHom.range_eq_top.mpr h.surj]

@[expose] noncomputable def TwoQuot.quotPCore (h : TwoQuot Θ) :
    (L ⧸ pCore 2 L) ≃* (L' ⧸ pCore 2 L') :=
  have hker : ((QuotientGroup.mk' (pCore 2 L')).comp Θ).ker = pCore 2 L := by
    rw [h.pCore_eq]
    ext x
    simp [QuotientGroup.eq_one_iff]
  (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _
      ((QuotientGroup.mk'_surjective _).comp h.surj))

theorem TwoQuot.quotPCore_mk (h : TwoQuot Θ) (l : L) :
    h.quotPCore (l : L ⧸ pCore 2 L) = ((Θ l : L') : L' ⧸ pCore 2 L') := rfl

structure CentralShort (Θ : L →* L') : Prop extends CentralTwoQuot Θ where
  inf_shortU : Θ.ker ⊓ shortU L = ⊥

@[expose] noncomputable def CentralShort.shortUMap (h : CentralShort Θ) :
    ↥(shortU L) ≃* ↥(shortU L') :=
  MulEquiv.ofBijective
    ((Θ.comp (shortU L).subtype).codRestrict (shortU L') (fun u => by
      rw [← h.map_shortU]
      exact ⟨u, u.2, rfl⟩))
    ⟨fun a b hab => by
      have h1 : Θ (a : L) = Θ (b : L) := congrArg Subtype.val hab
      have h2 : (a : L)⁻¹ * (b : L) ∈ Θ.ker ⊓ shortU L :=
        ⟨MonoidHom.mem_ker.mpr (by rw [map_mul, map_inv, h1, inv_mul_cancel]),
          (shortU L).mul_mem ((shortU L).inv_mem a.2) b.2⟩
      rw [h.inf_shortU, Subgroup.mem_bot, inv_mul_eq_one] at h2
      exact Subtype.ext h2,
     fun y => by
      have hy : (y : L') ∈ (shortU L).map Θ := by rw [h.map_shortU]; exact y.2
      obtain ⟨u, hu, hΘ⟩ := hy
      exact ⟨⟨u, hu⟩, Subtype.ext hΘ⟩⟩

theorem CentralShort.coe_shortUMap (h : CentralShort Θ) (u : ↥(shortU L)) :
    ((h.shortUMap u : ↥(shortU L')) : L') = Θ (u : L) := rfl

@[expose] noncomputable def CentralShort.shortIso (h : CentralShort Θ)
    (hU : ∀ u ∈ shortU L', ∀ o ∈ pCore 2 L', u * o = o * u) : ShortIso L L' where
  e := h.toCentralTwoQuot.quotPCore
  κ := h.shortUMap
  mem_C u := by
    rw [CentralShort.coe_shortUMap]
    unfold shortC
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨-, hc⟩
      refine ⟨u.2, Subgroup.mem_center_iff.mpr fun l => ?_⟩
      have hcomm : Θ (l * (u : L) * l⁻¹ * (u : L)⁻¹) = 1 := by
        have := Subgroup.mem_center_iff.mp hc (Θ l)
        simp only [map_mul, map_inv]
        rw [this]
        group
      have hmem : l * (u : L) * l⁻¹ * (u : L)⁻¹ ∈ Θ.ker ⊓ shortU L :=
        ⟨hcomm, (shortU L).mul_mem
          ((inferInstance : (shortU L).Normal).conj_mem _ u.2 l) ((shortU L).inv_mem u.2)⟩
      rw [h.inf_shortU, Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hmem
      exact hmem
    · rintro ⟨-, hc⟩
      refine ⟨(h.shortUMap u).2, Subgroup.mem_center_iff.mpr fun l' => ?_⟩
      obtain ⟨l, rfl⟩ := h.surj l'
      have := Subgroup.mem_center_iff.mp hc l
      rw [← map_mul, ← map_mul, this]
  conj l₁ l₂ hl u hu := by
    simp only [CentralShort.coe_shortUMap]
    have hq : (Θ l₁ : L' ⧸ pCore 2 L') = (l₂ : L' ⧸ pCore 2 L') := hl
    have ho : (Θ l₁)⁻¹ * l₂ ∈ pCore 2 L' := QuotientGroup.eq.mp hq
    have hu' := hU _ (h.shortUMap u).2 _ ho
    have hu'' : Θ (u : L) * ((Θ l₁)⁻¹ * l₂) = ((Θ l₁)⁻¹ * l₂) * Θ (u : L) := hu'
    set o := (Θ l₁)⁻¹ * l₂ with ho'
    have hl2 : l₂ = Θ l₁ * o := by rw [ho']; group
    rw [map_mul, map_mul, map_inv, hl2]
    calc Θ l₁ * Θ (u : L) * (Θ l₁)⁻¹ = Θ l₁ * (Θ (u : L) * o) * o⁻¹ * (Θ l₁)⁻¹ := by group
      _ = Θ l₁ * (o * Θ (u : L)) * o⁻¹ * (Θ l₁)⁻¹ := by rw [hu'']
      _ = Θ l₁ * o * Θ (u : L) * (Θ l₁ * o)⁻¹ := by group

theorem conj_pow_of_central {x o z : L} (hz : ∀ l : L, l * z = z * l) (h : x * o * x⁻¹ = z * o)
    (n : ℕ) : x ^ n * o * (x ^ n)⁻¹ = z ^ n * o := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : x ^ (n + 1) * o * (x ^ (n + 1))⁻¹ = x * (x ^ n * o * (x ^ n)⁻¹) * x⁻¹ := by
      rw [pow_succ']
      group
    have h3 : x * z ^ n * x⁻¹ = z ^ n := by
      have hc : Commute x z := hz x
      rw [(hc.pow_right n).eq]
      group
    have h2 : x * (z ^ n * o) * x⁻¹ = (x * z ^ n * x⁻¹) * (x * o * x⁻¹) := by group
    rw [h1, ih, h2, h3, h, pow_succ]
    group

theorem CentralTwoQuot.exists_exponent [Finite L] (h : CentralTwoQuot Θ) :
    ∃ a : ℕ, ∀ z ∈ Θ.ker, z ^ 2 ^ a = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := h.two.exists_card_eq
  refine ⟨a, fun z hz => ?_⟩
  have := pow_card_eq_one' (G := ↥Θ.ker) (x := ⟨z, hz⟩)
  rw [ha] at this
  exact congrArg Subtype.val this

theorem CentralTwoQuot.isCharacteristicP_of (h : CentralTwoQuot Θ) (h' : IsCharacteristicP 2 L') :
    IsCharacteristicP 2 L := by
  intro g hg
  rw [h.pCore_eq, Subgroup.mem_comap]
  refine h' ?_
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hx' : x ∈ (pCore 2 L).map Θ := by rw [h.map_pCore]; exact hx
  obtain ⟨y, hy, rfl⟩ := hx'
  have := Subgroup.mem_centralizer_iff.mp hg y hy
  rw [← map_mul, ← map_mul, this]

theorem CentralTwoQuot.isCharacteristicP_quot [Finite L] (h : CentralTwoQuot Θ)
    (hL : IsCharacteristicP 2 L) : IsCharacteristicP 2 L' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := h.exists_exponent
  intro g' hg'
  obtain ⟨g, rfl⟩ := h.surj g'
  let D : Subgroup L := (Subgroup.centralizer (pCore 2 L' : Set L')).comap Θ
  have hDn : D.Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    intro o ho
    have hx' := Subgroup.mem_centralizer_iff.mp hx
    have ho' : (Θ g)⁻¹ * o * Θ g ∈ pCore 2 L' := by
      have := (pCore_normal (p := 2) (G := L')).conj_mem o ho (Θ g)⁻¹
      simpa using this
    have h1 := hx' _ ho'
    simp only [map_mul, map_inv]
    calc o * (Θ g * Θ x * (Θ g)⁻¹)
        = Θ g * ((Θ g)⁻¹ * o * Θ g * Θ x) * (Θ g)⁻¹ := by group
      _ = Θ g * (Θ x * ((Θ g)⁻¹ * o * Θ g)) * (Θ g)⁻¹ := by rw [h1]
      _ = Θ g * Θ x * (Θ g)⁻¹ * o := by group
  have hD2 : IsPGroup 2 ↥D := by
    rintro ⟨d, hd⟩
    have hd' := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_comap.mp hd)
    have hcent : d ^ 2 ^ a ∈ Subgroup.centralizer (pCore 2 L : Set L) := by
      rw [Subgroup.mem_centralizer_iff]
      intro o ho
      set z := d * o * d⁻¹ * o⁻¹ with hz
      have hzker : z ∈ Θ.ker := by
        rw [MonoidHom.mem_ker, hz]
        simp only [map_mul, map_inv]
        have ho2 : Θ o ∈ pCore 2 L' := by
          have : Θ o ∈ (pCore 2 L).map Θ := ⟨o, ho, rfl⟩
          rwa [h.map_pCore] at this
        have := hd' _ ho2
        rw [← this]
        group
      have hzc : ∀ l : L, l * z = z * l := fun l =>
        (Subgroup.mem_center_iff.mp (h.central hzker) l)
      have hdo : d * o * d⁻¹ = z * o := by rw [hz]; group
      have := conj_pow_of_central hzc hdo (2 ^ a)
      rw [ha z hzker, one_mul] at this
      calc o * d ^ 2 ^ a = (d ^ 2 ^ a * o * (d ^ 2 ^ a)⁻¹) * d ^ 2 ^ a := by rw [this]
        _ = d ^ 2 ^ a * o := by group
    have hmem : d ^ 2 ^ a ∈ pCore 2 L := hL hcent
    obtain ⟨b, hb⟩ := (pCore_isPGroup (p := 2) (G := L)) ⟨d ^ 2 ^ a, hmem⟩
    refine ⟨a + b, Subtype.ext ?_⟩
    have hb' : (d ^ 2 ^ a) ^ 2 ^ b = 1 := congrArg Subtype.val hb
    rw [← pow_mul, ← pow_add] at hb'
    simpa using hb'
  have hle : D ≤ pCore 2 L := le_sSup ⟨hDn, hD2⟩
  have hgD : g ∈ D := hg'
  have := hle hgD
  rw [h.pCore_eq, Subgroup.mem_comap] at this
  exact this

theorem shortU_le_pCore' (M : Type) [Group M] : shortU M ≤ pCore 2 M :=
  Subgroup.commutator_le_left _ _

omit [Group L'] in
theorem commutator_mem_shortU {u o : L} (hu : u ∈ shortU L) : u * o * u⁻¹ * o⁻¹ ∈ shortU L := by
  have h1 : u * o * u⁻¹ * o⁻¹ = u * (o * u⁻¹ * o⁻¹) := by group
  rw [h1]
  exact (shortU L).mul_mem hu
    ((inferInstance : (shortU L).Normal).conj_mem _ ((shortU L).inv_mem hu) o)

theorem CentralTwoQuot.shortU_comm_quot (h : CentralTwoQuot Θ)
    (hL : ∀ u ∈ shortU L, ∀ o ∈ pCore 2 L, u * o = o * u) :
    ∀ u ∈ shortU L', ∀ o ∈ pCore 2 L', u * o = o * u := by
  intro u hu o ho
  have hu' : u ∈ (shortU L).map Θ := by rw [h.map_shortU]; exact hu
  have ho' : o ∈ (pCore 2 L).map Θ := by rw [h.map_pCore]; exact ho
  obtain ⟨u₀, hu₀, rfl⟩ := hu'
  obtain ⟨o₀, ho₀, rfl⟩ := ho'
  rw [← map_mul, ← map_mul, hL u₀ hu₀ o₀ ho₀]

theorem CentralShort.shortU_comm (h : CentralShort Θ)
    (hL' : ∀ u ∈ shortU L', ∀ o ∈ pCore 2 L', u * o = o * u) :
    ∀ u ∈ shortU L, ∀ o ∈ pCore 2 L, u * o = o * u := by
  intro u hu o ho
  have hΘu : Θ u ∈ shortU L' := by rw [← h.map_shortU]; exact ⟨u, hu, rfl⟩
  have hΘo : Θ o ∈ pCore 2 L' := by rw [← h.map_pCore]; exact ⟨o, ho, rfl⟩
  have hmem : u * o * u⁻¹ * o⁻¹ ∈ Θ.ker ⊓ shortU L := by
    refine ⟨MonoidHom.mem_ker.mpr ?_, commutator_mem_shortU hu⟩
    simp only [map_mul, map_inv]
    rw [hL' _ hΘu _ hΘo]
    group
  rw [h.inf_shortU, Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hmem
  exact hmem

variable [Finite L] [Finite L']

theorem CentralShort.isShortGroup_of (h : CentralShort Θ) (hres : oResidualTwo L = ⊤)
    (h' : IsShortGroup L') : IsShortGroup L := by
  have hU' : ∀ u ∈ shortU L', ∀ o ∈ pCore 2 L', u * o = o * u := fun u hu o ho =>
    ((shortU_le_center_iff.mp h'.U_le_center) u hu).2 o ho
  have hUc := h.shortU_comm hU'
  let S := h.shortIso hU'
  refine ⟨?_, hres, S.symm.quotient_type h'.quotient_type, ?_, S.symm.nonzero h'.nonzero,
    S.symm.irreducible h'.irreducible⟩
  · exact (isCharacteristicP_iff_generalizedFitting_eq_pCore L 2).mp
      (h.toCentralTwoQuot.isCharacteristicP_of
        ((isCharacteristicP_iff_generalizedFitting_eq_pCore L' 2).mpr h'.fitting_eq))
  · rw [shortU_le_center_iff]
    intro u hu
    refine ⟨?_, hUc u hu⟩
    have hΘu : Θ u ∈ pCore 2 L' := shortU_le_pCore' L' (by rw [← h.map_shortU]; exact ⟨u, hu, rfl⟩)
    rw [h.pCore_eq]
    exact hΘu

theorem CentralShort.isShortGroup_quot (h : CentralShort Θ) (hL : IsShortGroup L) :
    IsShortGroup L' := by
  have hUc : ∀ u ∈ shortU L, ∀ o ∈ pCore 2 L, u * o = o * u := fun u hu o ho =>
    ((shortU_le_center_iff.mp hL.U_le_center) u hu).2 o ho
  have hU' := h.toCentralTwoQuot.shortU_comm_quot hUc
  let S := h.shortIso hU'
  refine ⟨?_, ?_, S.quotient_type hL.quotient_type, ?_, S.nonzero hL.nonzero,
    S.irreducible hL.irreducible⟩
  · exact (isCharacteristicP_iff_generalizedFitting_eq_pCore L' 2).mp
      (h.toCentralTwoQuot.isCharacteristicP_quot
        ((isCharacteristicP_iff_generalizedFitting_eq_pCore L 2).mpr hL.fitting_eq))
  · rw [oResidualTwo_eq_top_iff]
    intro N' hN' hpow
    have hN : (N'.comap Θ).Normal := hN'.comap Θ
    have htop : N'.comap Θ = ⊤ := by
      refine (oResidualTwo_eq_top_iff.mp hL.residual_eq) _ hN fun g => ?_
      obtain ⟨k, hk⟩ := hpow (Θ g)
      exact ⟨k, by rw [Subgroup.mem_comap, map_pow]; exact hk⟩
    rw [eq_top_iff]
    intro x _
    obtain ⟨y, rfl⟩ := h.surj x
    have : y ∈ N'.comap Θ := by rw [htop]; trivial
    exact this
  · rw [shortU_le_center_iff]
    intro u hu
    refine ⟨shortU_le_pCore' L' hu, hU' u hu⟩

theorem CentralShort.inClassX_iff (h : CentralShort Θ) (hres : oResidualTwo L = ⊤) :
    InClassX L ↔ InClassX L' := by
  constructor
  · intro hL
    have hUc : ∀ u ∈ shortU L, ∀ o ∈ pCore 2 L, u * o = o * u := fun u hu o ho =>
      ((shortU_le_center_iff.mp hL.1.U_le_center) u hu).2 o ho
    let S := h.shortIso (h.toCentralTwoQuot.shortU_comm_quot hUc)
    refine ⟨h.isShortGroup_quot hL.1, ?_⟩
    rcases hL.2 with ⟨n, hn, hnat⟩ | ⟨n, hn, hnat⟩
    · obtain ⟨φ, hφ⟩ := isNaturalAltModule_iff.mp hnat
      exact Or.inl ⟨n, hn, isNaturalAltModule_iff.mpr ⟨_, S.symm.altModule hφ⟩⟩
    · exact Or.inr ⟨n, hn, S.symm.slModule hnat⟩
  · intro hL'
    have hU' : ∀ u ∈ shortU L', ∀ o ∈ pCore 2 L', u * o = o * u := fun u hu o ho =>
      ((shortU_le_center_iff.mp hL'.1.U_le_center) u hu).2 o ho
    let S := h.shortIso hU'
    refine ⟨h.isShortGroup_of hres hL'.1, ?_⟩
    rcases hL'.2 with ⟨n, hn, hnat⟩ | ⟨n, hn, hnat⟩
    · obtain ⟨φ, hφ⟩ := isNaturalAltModule_iff.mp hnat
      exact Or.inl ⟨n, hn, isNaturalAltModule_iff.mpr ⟨_, S.altModule hφ⟩⟩
    · exact Or.inr ⟨n, hn, S.slModule hnat⟩

end Central

section Arrow

variable {Γ Γ' : Type} [Group Γ] [Group Γ']

theorem arrowNat_of_central {Y X : Subgroup Γ} {Yb Xb : Subgroup Γ'} {ΘX : ↥X →* ↥Xb}
    {ΘY : ↥Y →* ↥Yb} (hX : CentralShort ΘX)
    (hU' : ∀ u ∈ shortU ↥Xb, ∀ o ∈ pCore 2 ↥Xb, u * o = o * u) (hY : CentralTwoQuot ΘY)
    (hYX : Y ≤ X) (hcompat : ∀ y : ↥Y, ((ΘY y : ↥Yb) : Γ') = ((ΘX ⟨y, hYX y.2⟩ : ↥Xb) : Γ'))
    (hsU : (shortU ↥Y).map Y.subtype ≤ (shortU ↥X).map X.subtype) (heq : Yb = Xb → Y = X)
    (harr : ArrowNat Yb Xb) : ArrowNat Y X := by
  rcases harr with h1 | ⟨a, b, φ, F, ⟨ψ⟩, hnat, hF, -, -, himg⟩
  · exact Or.inl (heq h1)
  · right
    let S := hX.shortIso hU'
    refine ⟨a, b, S.e.trans φ, F, ⟨hY.quotPCore.trans ψ⟩, S.altModule hnat, hF, hsU, hYX, ?_⟩
    rw [← himg]
    ext σ
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, QuotientGroup.mk'_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.trans_apply]
    constructor
    · rintro ⟨q, ⟨y', hy', rfl⟩, rfl⟩
      refine ⟨_, ⟨ΘX y', ?_, rfl⟩, rfl⟩
      rw [← hcompat ⟨y', hy'⟩]
      exact (ΘY ⟨y', hy'⟩).2
    · rintro ⟨q, ⟨z, hz, rfl⟩, rfl⟩
      obtain ⟨y, hy⟩ := hY.surj ⟨(z : Γ'), hz⟩
      refine ⟨_, ⟨⟨y.1, hYX y.2⟩, y.2, rfl⟩, ?_⟩
      have hz' : ΘX ⟨y.1, hYX y.2⟩ = z := by
        apply Subtype.ext
        rw [← hcompat y, hy]
      show φ (S.e (((⟨y.1, hYX y.2⟩ : ↥X) : ↥X ⧸ pCore 2 ↥X))) = φ ((z : ↥Xb ⧸ pCore 2 ↥Xb))
      rw [← hz']
      rfl

end Arrow


end CFSG.CGT.PushingUpLit.CGT6
