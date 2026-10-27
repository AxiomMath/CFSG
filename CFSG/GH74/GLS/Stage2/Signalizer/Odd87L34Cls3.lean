module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L34Facts

public section

open Subgroup CFSG CFSG.ComponentClassification.PSL3Four CFSG.GH74.GLS
  CFSG.GH74.GLS.Stage2.Signalizer CFSG.GH74.GLS.Stage2.Local

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

namespace Cls3

@[expose] def ConclG (G : Type) [Group G] (I : Subgroup G) (a : G) (X : Subgroup G) : Prop :=
  Nat.card ↥X = 3 ∧ X ⊓ I = ⊥ ∧ a ∉ I ⊔ X ∧ IsPGL3Four ↥(I ⊔ X) ∧
    I ⊓ centralizer ({a} : Set G) = I ⊓ centralizer (X : Set G) ∧
    IVK.IsL2 ↥(I ⊓ centralizer ({a} : Set G)) (fun q => q = 4) ∧
    (I ⊔ X ⊔ zpowers a) ⊓ centralizer ((I ⊓ centralizer ({a} : Set G) : Subgroup G) : Set G) =
      X ⊔ zpowers a

theorem l34Concl_of_equiv {Y : Type} [Group Y] [Finite Y] {G : Type} [Group G] (e : G ≃* MulAut Y)
    {I : Subgroup G} (hI : I.map e.toMonoidHom = innSub Y) {a : G} {X : Subgroup G}
    (h : ConclG G I a X) : L34Concl Y (e a) (X.map e.toMonoidHom) := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := h
  have hinj : Function.Injective e.toMonoidHom := e.injective
  have hsup : (I ⊔ X).map e.toMonoidHom = innSub Y ⊔ X.map e.toMonoidHom := by
    rw [Transport.map_sup, hI]
  have hJ : (I ⊓ centralizer ({a} : Set G)).map e.toMonoidHom =
      innSub Y ⊓ centralizer ({e a} : Set (MulAut Y)) := by
    rw [Transport.map_inf, hI, Transport.map_centralizer_singleton]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective hinj]
    exact c1
  · rw [← hI, ← Transport.map_inf, c2, Subgroup.map_bot]
  · intro hmem
    apply c3
    rw [← hsup] at hmem
    obtain ⟨b, hb, hba⟩ := Subgroup.mem_map.1 hmem
    have hba' : b = a := e.injective hba
    rwa [hba'] at hb
  · exact Transport.isPGL3Four_of_mulEquiv (Transport.subEquiv e hsup) c4
  · rw [← hJ, c5, Transport.map_inf, hI, Transport.map_centralizer]
  · exact Transport.isL2_of_mulEquiv (Transport.subEquiv e hJ) c6
  · have h7 := congrArg (Subgroup.map e.toMonoidHom) c7
    rw [Transport.map_inf, Transport.map_sup, Transport.map_sup, Transport.map_sup,
      Transport.map_zpowers, hI, Transport.map_centralizer, hJ] at h7
    exact h7

theorem eq_one_or_eq_or_eq_inv_of_mem_zpowers {G : Type*} [Group G] {g : G} (h : g ^ 3 = 1)
    {x : G} (hx : x ∈ zpowers g) : x = 1 ∨ x = g ∨ x = g⁻¹ := by
  obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hx
  have h3 : g ^ (3 : ℤ) = 1 := by exact_mod_cast h
  have hk : g ^ m = g ^ (m % 3) := by
    have hk3 : m = 3 * (m / 3) + m % 3 := by omega
    conv_lhs => rw [hk3]
    rw [zpow_add, zpow_mul, h3, one_zpow, one_mul]
  rcases (by omega : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2) with h0 | h1 | h2
  · left
    rw [hk, h0, zpow_zero]
  · right
    left
    rw [hk, h1, zpow_one]
  · right
    right
    rw [hk, h2]
    have : g ^ (2 : ℤ) * g = 1 := by
      calc g ^ (2 : ℤ) * g = g ^ (3 : ℤ) := by group
        _ = 1 := h3
    exact eq_inv_of_mul_eq_one_left this

section InR

variable {ζ : ↥R}

theorem ζ_pow_three (F : L34Facts (ζ : Equiv.Perm (Fin 42))) : ζ ^ 3 = 1 :=
  Subtype.ext (by simpa using F.z_cube)

theorem ζ_ne_one (F : L34Facts (ζ : Equiv.Perm (Fin 42))) : ζ ≠ 1 :=
  fun h => F.z_ne (congrArg Subtype.val h)

theorem card_zpowers (F : L34Facts (ζ : Equiv.Perm (Fin 42))) : Nat.card ↥(zpowers ζ) = 3 := by
  rw [Nat.card_zpowers]
  exact orderOf_eq_prime (ζ_pow_three F) (ζ_ne_one F)

theorem zpowers_inf_SR (F : L34Facts (ζ : Equiv.Perm (Fin 42))) :
    zpowers ζ ⊓ S.subgroupOf R = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxZ, hxS⟩ := Subgroup.mem_inf.1 hx
  replace hxS : (x : Equiv.Perm (Fin 42)) ∈ S := mem_subgroupOf.1 hxS
  rcases eq_one_or_eq_or_eq_inv_of_mem_zpowers (ζ_pow_three F) hxZ with h | h | h
  · rw [h]
    exact one_mem _
  · rw [h] at hxS
    exact absurd hxS F.z_notS
  · rw [h] at hxS
    exact absurd (by simpa using hxS) F.zi_notS

theorem a_not_mem_sup (F : L34Facts (ζ : Equiv.Perm (Fin 42))) :
    r₃R ∉ S.subgroupOf R ⊔ zpowers ζ := by
  intro hmem
  have : (S.subgroupOf R).Normal := S_normal
  obtain ⟨s, hs, y, hy, hsy⟩ := Subgroup.mem_sup_of_normal_left.1 hmem
  have hsy' : (s : Equiv.Perm (Fin 42)) * (y : Equiv.Perm (Fin 42)) = r₃ :=
    congrArg Subtype.val hsy
  have hsS : (s : Equiv.Perm (Fin 42)) ∈ S := mem_subgroupOf.1 hs
  rcases eq_one_or_eq_or_eq_inv_of_mem_zpowers (ζ_pow_three F) hy with h | h | h
  · rw [h] at hsy'
    apply not_mem_S_r₃
    rw [← hsy']
    simpa using hsS
  · rw [h] at hsy'
    apply F.rzi_notS
    have e : r₃ * (ζ : Equiv.Perm (Fin 42))⁻¹ = (s : Equiv.Perm (Fin 42)) := by
      rw [← hsy']
      group
    rw [e]
    exact hsS
  · rw [h] at hsy'
    apply F.rz_notS
    have e : r₃ * (ζ : Equiv.Perm (Fin 42)) = (s : Equiv.Perm (Fin 42)) := by
      rw [← hsy']
      simp
    rw [e]
    exact hsS

@[expose] noncomputable def equivOfMap {H : Subgroup ↥R} {H' : Subgroup (Equiv.Perm (Fin 42))}
    (h : H.map R.subtype = H') : ↥H ≃* ↥H' :=
  (Subgroup.equivMapOfInjective H R.subtype R.subtype_injective).trans (MulEquiv.subgroupCongr h)

theorem map_sup_subtype (F : L34Facts (ζ : Equiv.Perm (Fin 42))) :
    (S.subgroupOf R ⊔ zpowers ζ).map R.subtype = Odd87L34Out.NN := by
  have hzN : (ζ : Equiv.Perm (Fin 42)) ∈ Odd87L34Out.NN :=
    Odd87L34Out.odd_mem_NN ζ.2 F.z_cube
  rw [Subgroup.map_sup, map_subgroupOf_eq_of_le S_le_R, MonoidHom.map_zpowers]
  apply le_antisymm
  · exact sup_le (fun x hx => Subgroup.mem_sup_left hx) ((zpowers_le).2 hzN)
  · exact Odd87L34Out.NN_le_sup_of_not_mem hzN F.z_notS

theorem isPGL3Four_sup (F : L34Facts (ζ : Equiv.Perm (Fin 42)))
    (hPGL : IsPGL3Four ↥Odd87L34Out.NN) : IsPGL3Four ↥(S.subgroupOf R ⊔ zpowers ζ) :=
  Transport.isPGL3Four_of_mulEquiv (equivOfMap (map_sup_subtype F)).symm hPGL

theorem cent_eq (F : L34Facts (ζ : Equiv.Perm (Fin 42))) :
    S.subgroupOf R ⊓ centralizer ({r₃R} : Set ↥R) =
      S.subgroupOf R ⊓ centralizer ((zpowers ζ : Subgroup ↥R) : Set ↥R) := by
  ext x
  rw [Subgroup.mem_inf, Subgroup.mem_inf]
  refine and_congr_right fun hxS => ?_
  have hxS' : (x : Equiv.Perm (Fin 42)) ∈ S := mem_subgroupOf.1 hxS
  constructor
  · intro hx
    have hx1 : (x : Equiv.Perm (Fin 42)) * r₃ = r₃ * x :=
      congrArg Subtype.val (mem_centralizer_singleton_iff.1 hx)
    have hxC : (x : Equiv.Perm (Fin 42)) ∈ C₃ := ⟨mem_centralizer_singleton_iff.2 hx1, hxS'⟩
    have hxz : (x : Equiv.Perm (Fin 42)) * (ζ : Equiv.Perm (Fin 42)) =
        (ζ : Equiv.Perm (Fin 42)) * x := F.z_comm _ hxC
    have hc : Commute ζ x := Subtype.ext hxz.symm
    rw [mem_centralizer_iff]
    intro y hy
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hy
    exact (Commute.zpow_left hc m).eq
  · intro hx
    have hz : ζ * x = x * ζ := mem_centralizer_iff.1 hx ζ (mem_zpowers ζ)
    have hz' : (x : Equiv.Perm (Fin 42)) * (ζ : Equiv.Perm (Fin 42)) =
        (ζ : Equiv.Perm (Fin 42)) * x := (congrArg Subtype.val hz).symm
    exact mem_centralizer_singleton_iff.2 (Subtype.ext (F.cent_le _ hxS' hz'))

theorem map_cent_subtype :
    (S.subgroupOf R ⊓ centralizer ({r₃R} : Set ↥R)).map R.subtype = C₃ := by
  ext x
  constructor
  · rintro ⟨y, ⟨hyS, hyc⟩, rfl⟩
    exact ⟨mem_centralizer_singleton_iff.2
      (congrArg Subtype.val (mem_centralizer_singleton_iff.1 hyc)), mem_subgroupOf.1 hyS⟩
  · rintro ⟨hxc, hxS⟩
    exact ⟨⟨x, S_le_R hxS⟩, ⟨mem_subgroupOf.2 hxS,
      mem_centralizer_singleton_iff.2 (Subtype.ext (mem_centralizer_singleton_iff.1 hxc))⟩, rfl⟩

theorem isL2_cent (hL2 : IVK.IsL2 ↥C₃ (fun q => q = 4)) :
    IVK.IsL2 ↥(S.subgroupOf R ⊓ centralizer ({r₃R} : Set ↥R)) (fun q => q = 4) :=
  Transport.isL2_of_mulEquiv (equivOfMap map_cent_subtype).symm hL2

theorem centralizer_cent_le (F : L34Facts (ζ : Equiv.Perm (Fin 42))) :
    centralizer ((S.subgroupOf R ⊓ centralizer ({r₃R} : Set ↥R) : Subgroup ↥R) : Set ↥R) ≤
      zpowers ζ ⊔ zpowers r₃R := by
  intro w hw
  have hscan := F.scan (w : Equiv.Perm (Fin 42)) w.2 (fun d hd => by
    have hdR : d ∈ R := S_le_R hd.2
    have hdm : (⟨d, hdR⟩ : ↥R) ∈ S.subgroupOf R ⊓ centralizer ({r₃R} : Set ↥R) :=
      ⟨mem_subgroupOf.2 hd.2, mem_centralizer_singleton_iff.2
        (Subtype.ext (mem_centralizer_singleton_iff.1 hd.1))⟩
    exact congrArg Subtype.val (mem_centralizer_iff.1 hw _ hdm))
  have hZ : ζ ∈ zpowers ζ ⊔ zpowers r₃R := Subgroup.mem_sup_left (mem_zpowers ζ)
  have hA : r₃R ∈ zpowers ζ ⊔ zpowers r₃R := Subgroup.mem_sup_right (mem_zpowers r₃R)
  rcases hscan with h | h | h | h | h | h
  · rw [show w = 1 from Subtype.ext h]
    exact one_mem _
  · rw [show w = ζ from Subtype.ext h]
    exact hZ
  · rw [show w = ζ⁻¹ from Subtype.ext (by rw [Subgroup.coe_inv]; exact h)]
    exact inv_mem hZ
  · rw [show w = r₃R from Subtype.ext h]
    exact hA
  · rw [show w = ζ * r₃R from Subtype.ext h]
    exact mul_mem hZ hA
  · rw [show w = ζ⁻¹ * r₃R from Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_inv]; exact h)]
    exact mul_mem (inv_mem hZ) hA

theorem sup_inf_centralizer (F : L34Facts (ζ : Equiv.Perm (Fin 42))) :
    (S.subgroupOf R ⊔ zpowers ζ ⊔ zpowers r₃R) ⊓
        centralizer ((S.subgroupOf R ⊓ centralizer ({r₃R} : Set ↥R) : Subgroup ↥R) : Set ↥R) =
      zpowers ζ ⊔ zpowers r₃R := by
  apply le_antisymm
  · exact inf_le_right.trans (centralizer_cent_le F)
  · refine le_inf (sup_le (le_sup_of_le_left le_sup_right) le_sup_right) (sup_le ?_ ?_)
    · intro y hy
      rw [mem_centralizer_iff]
      intro x hx
      have hx' : x ∈ S.subgroupOf R ⊓ centralizer ((zpowers ζ : Subgroup ↥R) : Set ↥R) := by
        rwa [← cent_eq F]
      exact (mem_centralizer_iff.1 hx'.2 y hy).symm
    · intro y hy
      rw [mem_centralizer_iff]
      intro x hx
      obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hy
      exact (Commute.zpow_left (mem_centralizer_iff.1 hx.2 r₃R rfl) m).eq.symm

theorem conclG_class3 (F : L34Facts (ζ : Equiv.Perm (Fin 42)))
    (hPGL : IsPGL3Four ↥Odd87L34Out.NN) (hL2 : IVK.IsL2 ↥C₃ (fun q => q = 4)) :
    ConclG ↥R (S.subgroupOf R) r₃R (zpowers ζ) :=
  ⟨card_zpowers F, zpowers_inf_SR F, a_not_mem_sup F, isPGL3Four_sup F hPGL, cent_eq F,
    isL2_cent hL2, sup_inf_centralizer F⟩

end InR

section Model


@[expose] noncomputable def conjIso : ↥R ≃* MulAut ↥S :=
  MulEquiv.ofBijective conjAutS ⟨conjAutS_injective, conjAutS_surjective⟩

theorem map_SR_eq_innSub : (S.subgroupOf R).map conjIso.toMonoidHom = innSub ↥S := by
  ext α
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact ⟨⟨r, hr⟩, MulEquiv.ext fun s => Subtype.ext rfl⟩
  · rintro ⟨s, rfl⟩
    exact ⟨⟨s, S_le_R s.2⟩, s.2, MulEquiv.ext fun t => Subtype.ext rfl⟩

end Model

end Cls3

theorem class3_concl {z : Equiv.Perm (Fin 42)} (F : L34Facts z)
    (hPGL : IsPGL3Four ↥CFSG.GH74.GLS.Stage2.Signalizer.Odd87L34Out.NN)
    (hL2 : IVK.IsL2 ↥CFSG.ComponentClassification.PSL3Four.C₃ (fun q => q = 4)) :
    L34Concl ↥CFSG.ComponentClassification.PSL3Four.S (conjAutS r₃R)
      (Subgroup.zpowers (conjAutS ⟨z, F.z_mem⟩)) := by
  have h := Cls3.l34Concl_of_equiv Cls3.conjIso Cls3.map_SR_eq_innSub
    (Cls3.conclG_class3 (ζ := ⟨z, F.z_mem⟩) F hPGL hL2)
  rw [Transport.map_zpowers] at h
  exact h

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
