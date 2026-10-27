module

public import CFSG.CGT.PushingUpLit.A78L3.Swap
public import CFSG.CGT.PushingUpLit.A78S4.Pair
public import CFSG.CGT.PushingUpLit.A78S4.TJ

public section

namespace CFSG.CGT.PushingUpLit.A78S4

open CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.A78 CFSG.CGT.PushingUpLit.A78Sp4
open CFSG.CGT.PushingUpLit.A78L3
open CFSG.QuasithinUnique.Setup.Offender (card_eq_sq_of_involution)
open CFSG.ABGLocalTools
open Matrix
open scoped commutatorElement

section Field

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem card_fix_mul_sq (τ : F ≃+* F) (hτ1 : τ ≠ 1) (hτ2 : τ * τ = 1) {μ : F}
    (hμ : μ * τ μ = 1) : Nat.card {r : F // μ * τ r = r} ^ 2 = Nat.card F := by
  have hττ : ∀ r, τ (τ r) = r := fun r => by
    have := congrArg (fun σ : F ≃+* F => σ r) hτ2
    simpa using this
  let ψ : F →+ F :=
    { toFun := fun r => r + μ * τ r
      map_zero' := by simp
      map_add' := fun r r' => by rw [map_add]; ring }
  have hker : Nat.card ψ.ker = Nat.card {r : F // μ * τ r = r} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun r => ?_)
    rw [AddMonoidHom.mem_ker]
    show r + μ * τ r = 0 ↔ μ * τ r = r
    constructor
    · intro h0
      linear_combination h0 - CharTwo.add_self_eq_zero r
    · intro h0
      rw [h0, CharTwo.add_self_eq_zero]
  have hrange : Nat.card ψ.range = Nat.card {r : F // μ * τ r = r} := by
    refine Nat.card_congr (Equiv.ofBijective (fun y => ⟨y.1, ?_⟩) ⟨fun y y' hyy => ?_, ?_⟩)
    · obtain ⟨r, hr⟩ := y.2
      rw [← hr]
      show μ * τ (r + μ * τ r) = r + μ * τ r
      rw [map_add, map_mul, hττ]
      linear_combination r * hμ
    · exact Subtype.ext (congrArg (fun z : {r : F // μ * τ r = r} => z.1) hyy)
    · rintro ⟨s, hs⟩
      obtain ⟨r, hr⟩ := exists_add_mul_eq τ hτ1 hτ2 hs
      exact ⟨⟨s, r, hr⟩, rfl⟩
  have hkr := AddSubgroup.card_ker_mul_card_range ψ
  rw [hker, hrange] at hkr
  rw [pow_two, hkr]

theorem card_fix_mul_eq {e : ℕ} (he : e ≠ 0) (τ : GaloisField 2 e ≃+* GaloisField 2 e)
    (hτ1 : τ ≠ 1) (hτ2 : τ * τ = 1) {μ : GaloisField 2 e} (hμ : μ * τ μ = 1) :
    Nat.card {r : GaloisField 2 e // μ * τ r = r} = 2 ^ (e / 2) := by
  have h1 := card_fix_mul_sq τ hτ1 hτ2 hμ
  rw [GaloisField.card 2 e he] at h1
  exact L3Pair.eq_two_pow_half h1.symm

end Field

namespace S4Pair

variable {G : Type} [Group G] [Finite G] {L₁ L₂ V W Z Z₂ T : Subgroup G} {e : ℕ}
  (P : S4Pair G L₁ L₂ V W Z Z₂ T e)

include P

theorem Z_le_N' : Z ≤ W ⊓ V := by
  have := P.side₁.Z_le_N
  rwa [inf_comm] at this

section ZCoord

variable {D₂ : NatCoordK G L₂ W Z₂ (GaloisField 2 e)} (fr₂ : S4Side.Frame P.side₂ D₂)

include fr₂

theorem zc_inj {z z' : G} (hz : z ∈ Z) (hz' : z' ∈ Z) (h : fr₂.c z = fr₂.c z') : z = z' := by
  have h1 := fr₂.c_inj_of_inf (P.Z_le_N' hz) (P.Z_le_N' hz') h
  have h2 : z * z'⁻¹ ∈ Z ⊓ Z₂ := Subgroup.mem_inf.2 ⟨mul_mem hz (inv_mem hz'), h1⟩
  rw [P.inf_Z, Subgroup.mem_bot] at h2
  exact mul_inv_eq_one.1 h2

theorem zc_surj (hZ : Z ≠ ⊥) (r : GaloisField 2 e) : ∃ z ∈ Z, fr₂.c z = r := by
  have hinj : Function.Injective (fun z : ↥Z => fr₂.c z) := fun z z' hzz =>
    Subtype.ext (P.zc_inj fr₂ z.2 z'.2 hzz)
  have hcard : Nat.card (GaloisField 2 e) ≤ Nat.card ↥Z := by
    rw [P.card_Z hZ, P.side₁.card_F]
  obtain ⟨z, hz⟩ := (hinj.bijective_of_nat_card_le hcard).2 r
  exact ⟨z, z.2, hz⟩

theorem zc_conj {t : G} (ht : t ∈ T) : ∃ μ : GaloisField 2 e, ∀ z ∈ Z,
    t * z * t⁻¹ ∈ Z ∧ fr₂.c (t * z * t⁻¹) = μ * P.side₂.sig D₂ ⟨t, ht⟩ (fr₂.c z) := by
  obtain ⟨μ, hμ⟩ := fr₂.act_n₀ ht
  exact ⟨μ, fun z hz => ⟨conj_mem_of_mem_normalizer (P.side₁.T_le_Z ht) hz,
    (fr₂.c_conj ht hμ (P.Z_le_N' hz)).2⟩⟩

end ZCoord

theorem exists_mul_conj_eq_Z (hZ : Z ≠ ⊥) {a : G} (ha : a ∈ T) (haJ : a ∉ V ⊔ W)
    (haa : a * a ∈ V) {z : G} (hz : z ∈ Z) (hfix : a * z * a⁻¹ = z) :
    ∃ z' ∈ Z, z' * (a * z' * a⁻¹) = z := by
  obtain ⟨D₂⟩ := P.side₂.nat
  obtain ⟨fr₂⟩ := P.side₂.exists_frame D₂
  have haJ₂ : a ∉ W ⊔ V := by rwa [sup_comm]
  have haa₂ : a * a ∈ W ⊔ V := Subgroup.mem_sup_right haa
  have hτ1 := P.side₂.sig_ne_one D₂ ha haJ₂
  have hτ2 := P.side₂.sig_sq_of_sq_mem D₂ ha haa₂
  obtain ⟨μ, hμ⟩ := P.zc_conj fr₂ ha
  have hs : μ * P.side₂.sig D₂ ⟨a, ha⟩ (fr₂.c z) = fr₂.c z := by
    rw [← (hμ z hz).2, hfix]
  obtain ⟨r, hr⟩ := exists_add_mul_eq _ hτ1 hτ2 hs
  obtain ⟨z', hz', hz'r⟩ := P.zc_surj fr₂ hZ r
  refine ⟨z', hz', P.zc_inj fr₂ (mul_mem hz' (hμ z' hz').1) hz ?_⟩
  rw [fr₂.c_mul (P.Z_le_N' hz').1 (P.Z_le_N' (hμ z' hz').1).1, (hμ z' hz').2, hz'r, hr]

theorem exists_mul_conj_eq (hZ : Z ≠ ⊥) {a : G} (ha : a ∈ T) (haJ : a ∉ V ⊔ W)
    (haa : a * a ∈ V) {v : G} (hv : v ∈ V) (hfix : a * v * a⁻¹ = v) :
    ∃ u ∈ V, u * (a * u * a⁻¹) = v := by
  obtain ⟨D⟩ := P.side₁.nat
  have haK := P.side₁.T_le_NVK ha
  have hb := P.side₁.semInv_of_sq_mem D ha haa
  have hσ := P.side₁.exists_sig_ne D ha haJ
  have hcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy =>
    (P.side₁.jst.abelian_V x hx y hy).eq
  have hconj : ∀ x ∈ V, a * x * a⁻¹ ∈ V := fun x hx => conj_mem_of_mem_normalizer haK.1 hx
  have hw : D.act a (D.κ v) = D.κ v := by rw [NatCoordK.act_κ haK hv, hfix]
  obtain ⟨w, hwv⟩ := exists_add_semInv_eq hσ hb hw
  set u₁ := D.sec w with hu₁
  have hu₁V : u₁ ∈ V := D.sec_mem w
  have hκ : D.κ (u₁ * (a * u₁ * a⁻¹)) = D.κ v := by
    rw [D.κ_mul _ hu₁V _ (hconj _ hu₁V), ← NatCoordK.act_κ haK hu₁V, D.κ_sec, hwv]
  have hd := (D.κ_eq_iff (mul_mem hu₁V (hconj _ hu₁V)) hv).1 hκ
  set y := u₁ * (a * u₁ * a⁻¹) with hy
  have hyV : y ∈ V := mul_mem hu₁V (hconj _ hu₁V)
  have hay : a * y * a⁻¹ = y := by
    have h1 : (a * a) * u₁ * (a * a)⁻¹ = u₁ := by
      rw [hcomm _ haa u₁ hu₁V]
      group
    calc a * y * a⁻¹ = (a * u₁ * a⁻¹) * ((a * a) * u₁ * (a * a)⁻¹) := by rw [hy]; group
      _ = (a * u₁ * a⁻¹) * u₁ := by rw [h1]
      _ = y := by rw [hy, hcomm _ (hconj _ hu₁V) _ hu₁V]
  have hzZ : v * y⁻¹ ∈ Z := by
    have := hd
    rw [show y * v⁻¹ = (v * y⁻¹)⁻¹ by group] at this
    simpa using inv_mem this
  have hzfix : a * (v * y⁻¹) * a⁻¹ = v * y⁻¹ := by
    calc a * (v * y⁻¹) * a⁻¹ = (a * v * a⁻¹) * (a * y * a⁻¹)⁻¹ := by group
      _ = v * y⁻¹ := by rw [hfix, hay]
  obtain ⟨z', hz', hz'eq⟩ := P.exists_mul_conj_eq_Z hZ ha haJ haa hzZ hzfix
  have hz'V := P.side₁.Z_le_V hz'
  refine ⟨z' * u₁, mul_mem hz'V hu₁V, ?_⟩
  have e1 : z' * u₁ * (a * (z' * u₁) * a⁻¹) = (z' * (a * z' * a⁻¹)) * y := by
    rw [hy]
    have h2 : u₁ * (a * z' * a⁻¹) = (a * z' * a⁻¹) * u₁ := hcomm _ hu₁V _ (hconj _ hz'V)
    calc z' * u₁ * (a * (z' * u₁) * a⁻¹) = z' * (u₁ * (a * z' * a⁻¹)) * (a * u₁ * a⁻¹) := by
          group
      _ = z' * ((a * z' * a⁻¹) * u₁) * (a * u₁ * a⁻¹) := by rw [h2]
      _ = z' * (a * z' * a⁻¹) * (u₁ * (a * u₁ * a⁻¹)) := by group
  rw [e1, hz'eq]
  group

section Involution

variable (hZ : Z ≠ ⊥) {f : G} (hf : f ∈ T) (hfJ : f ∉ V ⊔ W) (hff : f * f = 1)

include hf hfJ hff

theorem even_e : Even e := by
  obtain ⟨D⟩ := P.side₁.nat
  exact P.side₁.even_of_involution D hf hfJ hff

include hZ

theorem card_CZ : Nat.card ↥(Z ⊓ Subgroup.centralizer ({f} : Set G)) = 2 ^ (e / 2) := by
  obtain ⟨D₂⟩ := P.side₂.nat
  obtain ⟨fr₂⟩ := P.side₂.exists_frame D₂
  have hfJ₂ : f ∉ W ⊔ V := by rwa [sup_comm]
  have hτ1 := P.side₂.sig_ne_one D₂ hf hfJ₂
  have hτ2 := P.side₂.sig_sq D₂ hf hff
  obtain ⟨μ, hμ⟩ := P.zc_conj fr₂ hf
  have hfi : f⁻¹ = f := inv_eq_of_mul_eq_one_right hff
  have hμτ : μ * P.side₂.sig D₂ ⟨f, hf⟩ μ = 1 := by
    obtain ⟨z₁, hz₁, hz₁1⟩ := P.zc_surj fr₂ hZ 1
    have h1 := (hμ _ (hμ z₁ hz₁).1).2
    rw [(hμ z₁ hz₁).2, hz₁1] at h1
    simp only [map_one, mul_one] at h1
    have e1 : f * (f * z₁ * f⁻¹) * f⁻¹ = z₁ := by
      rw [hfi, show f * (f * z₁ * f) * f = (f * f) * z₁ * (f * f) by group, hff]
      group
    rw [e1, hz₁1] at h1
    exact h1.symm
  rw [← card_fix_mul_eq P.side₁.e_ne_zero _ hτ1 hτ2 hμτ]
  refine Nat.card_congr (Equiv.ofBijective (fun z => ⟨fr₂.c z, ?_⟩) ⟨fun z z' hzz => ?_, ?_⟩)
  · have hz := z.2
    have hfz : f * z * f⁻¹ = z := by
      have := Subgroup.mem_centralizer_singleton_iff.1 hz.2
      rw [← this]
      group
    rw [← (hμ z hz.1).2, hfz]
  · exact Subtype.ext (P.zc_inj fr₂ z.2.1 z'.2.1
      (congrArg (fun y : {r : GaloisField 2 e // μ * _ = r} => y.1) hzz))
  · rintro ⟨r, hr⟩
    obtain ⟨z, hz, hzr⟩ := P.zc_surj fr₂ hZ r
    have hfz : f * z * f⁻¹ = z := by
      refine P.zc_inj fr₂ (hμ z hz).1 hz ?_
      rw [(hμ z hz).2, hzr, hr]
    refine ⟨⟨z, hz, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩, Subtype.ext hzr⟩
    calc z * f = f * z * f⁻¹ * f := by rw [hfz]
      _ = f * z := by group

theorem card_CV : Nat.card ↥(V ⊓ Subgroup.centralizer ({f} : Set G)) = 2 ^ (3 * (e / 2)) := by
  obtain ⟨D⟩ := P.side₁.nat
  have hfK := P.side₁.T_le_NVK hf
  have hb := P.side₁.semInv D hf hff
  have hσ := P.side₁.exists_sig_ne D hf hfJ
  have hfi : f⁻¹ = f := inv_eq_of_mul_eq_one_right hff
  have hcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy =>
    (P.side₁.jst.abelian_V x hx y hy).eq
  have hconj : ∀ x ∈ V, f * x * f⁻¹ ∈ V := fun x hx => conj_mem_of_mem_normalizer hfK.1 hx
  let φ : ↥(V ⊓ Subgroup.centralizer ({f} : Set G)) →* Multiplicative (Fin 2 → GaloisField 2 e) :=
    { toFun := fun v => Multiplicative.ofAdd (D.κ v)
      map_one' := by
        show Multiplicative.ofAdd (D.κ 1) = 1
        rw [D.κ_one]
        rfl
      map_mul' := fun v w => by
        show Multiplicative.ofAdd (D.κ ((v : G) * w)) = _
        rw [D.κ_mul _ v.2.1 _ w.2.1, ofAdd_add] }
  have hker : Nat.card φ.ker = 2 ^ (e / 2) := by
    rw [← P.card_CZ hZ hf hfJ hff]
    refine Nat.card_congr (Equiv.ofBijective (fun v => ⟨v.1.1, ?_⟩) ⟨?_, ?_⟩)
    · have hv := v.1.2
      have h0 : D.κ v.1.1 = 0 := Multiplicative.ofAdd.injective v.2
      exact Subgroup.mem_inf.2 ⟨(D.κ_eq_zero _ hv.1).1 h0, hv.2⟩
    · intro v v' hvv
      exact Subtype.ext (Subtype.ext
        (congrArg (fun z : ↥(Z ⊓ Subgroup.centralizer ({f} : Set G)) => (z : G)) hvv))
    · rintro ⟨z, hzZ, hzC⟩
      refine ⟨⟨⟨z, P.side₁.Z_le_V hzZ, hzC⟩, ?_⟩, rfl⟩
      show Multiplicative.ofAdd (D.κ z) = 1
      rw [D.κ_of_mem_K hzZ]
      rfl
  have hrange : Nat.card φ.range = 2 ^ e := by
    rw [← P.side₁.card_F, ← card_fixSet hσ hb]
    refine Nat.card_congr (Equiv.ofBijective (fun y => ⟨Multiplicative.toAdd y.1, ?_⟩)
      ⟨fun y y' hyy => ?_, ?_⟩)
    · obtain ⟨v, hv⟩ := y.2
      rw [← hv]
      show D.act f (D.κ v) = D.κ v
      rw [NatCoordK.act_κ hfK v.2.1]
      congr 1
      have := Subgroup.mem_centralizer_singleton_iff.1 v.2.2
      rw [← this]
      group
    · exact Subtype.ext (Multiplicative.toAdd.injective
        (congrArg (fun z : ↥(fixSet (D.act f)) => (z : Fin 2 → GaloisField 2 e)) hyy))
    · rintro ⟨w, hw⟩
      obtain ⟨w', hw'⟩ := exists_add_semInv_eq hσ hb hw
      set u := D.sec w' with hu
      have huV : u ∈ V := D.sec_mem w'
      have hfix : f * (u * (f * u * f⁻¹)) * f⁻¹ = u * (f * u * f⁻¹) := by
        calc f * (u * (f * u * f⁻¹)) * f⁻¹ = (f * u * f⁻¹) * ((f * f) * u * (f * f)⁻¹) := by
              group
          _ = (f * u * f⁻¹) * u := by rw [hff]; group
          _ = u * (f * u * f⁻¹) := hcomm _ (hconj _ huV) _ huV
      have hmem : u * (f * u * f⁻¹) ∈ V ⊓ Subgroup.centralizer ({f} : Set G) := by
        refine Subgroup.mem_inf.2 ⟨mul_mem huV (hconj _ huV),
          Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
        calc u * (f * u * f⁻¹) * f = f * (u * (f * u * f⁻¹)) * f⁻¹ * f := by rw [hfix]
          _ = f * (u * (f * u * f⁻¹)) := by group
      refine ⟨⟨φ ⟨_, hmem⟩, ⟨_, hmem⟩, rfl⟩, Subtype.ext ?_⟩
      show D.κ (u * (f * u * f⁻¹)) = w
      rw [D.κ_mul _ huV _ (hconj _ huV), ← NatCoordK.act_κ hfK huV, D.κ_sec, hw']
  have hkr := Subgroup.card_ker_mul_card_range φ
  rw [hker, hrange] at hkr
  rw [← hkr, ← pow_add]
  obtain ⟨k, hk⟩ := P.even_e hf hfJ hff
  congr 1
  omega

theorem card_CN : Nat.card ↥((V ⊓ W) ⊓ Subgroup.centralizer ({f} : Set G)) = 2 ^ e := by
  have hfJ₂ : f ∉ W ⊔ V := by rwa [sup_comm]
  have hZ₂ := P.Z₂_ne_bot hZ
  have h1 := P.card_CZ hZ hf hfJ hff
  have h2 := P.symm.card_CZ hZ₂ hf hfJ₂ hff
  have hfi : f⁻¹ = f := inv_eq_of_mul_eq_one_right hff
  let g : ↥(Z ⊓ Subgroup.centralizer ({f} : Set G)) × ↥(Z₂ ⊓ Subgroup.centralizer ({f} : Set G)) →
      ↥((V ⊓ W) ⊓ Subgroup.centralizer ({f} : Set G)) := fun p =>
    ⟨p.1 * p.2, Subgroup.mem_inf.2 ⟨mul_mem (P.side₁.Z_le_N p.1.2.1) (P.Z₂_le_N p.2.2.1),
      mul_mem p.1.2.2 p.2.2.2⟩⟩
  have hg : Function.Bijective g := by
    refine ⟨fun p p' hpp => ?_, fun n => ?_⟩
    · have h3 : ((p.1 : G) * p.2) = p'.1 * p'.2 := congrArg Subtype.val hpp
      have h4 : (p'.1 : G)⁻¹ * p.1 = p'.2 * (p.2 : G)⁻¹ := by
        calc (p'.1 : G)⁻¹ * p.1 = (p'.1 : G)⁻¹ * (p.1 * p.2) * (p.2 : G)⁻¹ := by group
          _ = (p'.1 : G)⁻¹ * (p'.1 * p'.2) * (p.2 : G)⁻¹ := by rw [h3]
          _ = p'.2 * (p.2 : G)⁻¹ := by group
      have h5 : (p'.1 : G)⁻¹ * p.1 ∈ Z ⊓ Z₂ := Subgroup.mem_inf.2
        ⟨mul_mem (inv_mem p'.1.2.1) p.1.2.1, by rw [h4]; exact mul_mem p'.2.2.1 (inv_mem p.2.2.1)⟩
      rw [P.inf_Z, Subgroup.mem_bot] at h5
      have hz : (p.1 : G) = p'.1 := by
        have := congrArg (fun y => (p'.1 : G) * y) h5
        simpa using this
      have hz₂ : (p.2 : G) = p'.2 := by
        rw [hz] at h3
        exact mul_left_cancel h3
      exact Prod.ext (Subtype.ext hz) (Subtype.ext hz₂)
    · obtain ⟨z, hz, z₂, hz₂, hzz⟩ := P.exists_decomp hZ (n.2 : (n : G) ∈ (V ⊓ W) ⊓ _).1
      have hn : f * (n : G) * f⁻¹ = n := by
        have := Subgroup.mem_centralizer_singleton_iff.1 n.2.2
        rw [← this]
        group
      have hfz : f * z * f⁻¹ ∈ Z := conj_mem_of_mem_normalizer (P.side₁.T_le_Z hf) hz
      have hfz₂ : f * z₂ * f⁻¹ ∈ Z₂ := conj_mem_of_mem_normalizer (P.side₂.T_le_Z hf) hz₂
      have h3 : (f * z * f⁻¹) * (f * z₂ * f⁻¹) = z * z₂ := by
        rw [hzz, ← hn, ← hzz]
        group
      have h4 : (z : G)⁻¹ * (f * z * f⁻¹) = z₂ * (f * z₂ * f⁻¹)⁻¹ := by
        calc (z : G)⁻¹ * (f * z * f⁻¹) =
              z⁻¹ * ((f * z * f⁻¹) * (f * z₂ * f⁻¹)) * (f * z₂ * f⁻¹)⁻¹ := by group
          _ = z⁻¹ * (z * z₂) * (f * z₂ * f⁻¹)⁻¹ := by rw [h3]
          _ = z₂ * (f * z₂ * f⁻¹)⁻¹ := by group
      have h5 : z⁻¹ * (f * z * f⁻¹) ∈ Z ⊓ Z₂ := Subgroup.mem_inf.2
        ⟨mul_mem (inv_mem hz) hfz, by rw [h4]; exact mul_mem hz₂ (inv_mem hfz₂)⟩
      rw [P.inf_Z, Subgroup.mem_bot] at h5
      have hfz' : f * z * f⁻¹ = z := by
        have := congrArg (fun y => z * y) h5
        simpa using this
      have hfz₂' : f * z₂ * f⁻¹ = z₂ := by
        rw [hfz'] at h3
        exact mul_left_cancel h3
      have hzC : z ∈ Subgroup.centralizer ({f} : Set G) := by
        refine Subgroup.mem_centralizer_singleton_iff.2 ?_
        calc z * f = f * z * f⁻¹ * f := by rw [hfz']
          _ = f * z := by group
      have hz₂C : z₂ ∈ Subgroup.centralizer ({f} : Set G) := by
        refine Subgroup.mem_centralizer_singleton_iff.2 ?_
        calc z₂ * f = f * z₂ * f⁻¹ * f := by rw [hfz₂']
          _ = f * z₂ := by group
      exact ⟨(⟨z, Subgroup.mem_inf.2 ⟨hz, hzC⟩⟩, ⟨z₂, Subgroup.mem_inf.2 ⟨hz₂, hz₂C⟩⟩),
        Subtype.ext hzz⟩
  rw [← Nat.card_eq_of_bijective g hg, Nat.card_prod, h1, h2, ← pow_add]
  obtain ⟨k, hk⟩ := P.even_e hf hfJ hff
  congr 1
  omega

end Involution

end S4Pair

end CFSG.CGT.PushingUpLit.A78S4
