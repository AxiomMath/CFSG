module

public import CFSG.GH74.GLS.C3.Layer1.Thm1P38Env
public import CFSG.GH74.GLS.C3.Layer1.Thm1G33Aux
public import CFSG.GH74.GLS.C3.Layer1.Thm1Layer
public import CFSG.GH74.GLS.C3.Layer1.Thm1P38Fus
public import CFSG.GH74.GLS.C3.Layer1.Thm1P38Lift

public section

namespace CFSG.GH74.GLS.C3.Layer1.Thm1P38

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.C3.Layer1
  CFSG.GH74.GLS.C3.Layer1.Thm1
open scoped commutatorElement

variable {G : Type} [Group G]

theorem mem_zpowers_of_two_element [Finite G] {H : Subgroup G} {f q : G}
    (hS : IsSylowOf 2 (zpowers f) H) (hfc : ∀ h ∈ H, h * f = f * h) (hqH : q ∈ H)
    (hq : ∃ k : ℕ, q ^ (2 ^ k) = 1) : q ∈ zpowers f := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzp : IsPGroup 2 ↥(zpowers q) := Thm1.isPGroup_zpowers_of_pow_eq_one hq
  obtain ⟨T', hqT', hT'H, hT'p, hT'idx⟩ := P34.exists_sylow_ge (N := H) (zpowers_le.2 hqH) hzp
  have hT' : IsSylowOf 2 T' H := isSylowOf_iff.2 ⟨hT'H, hT'p, hT'idx⟩
  obtain ⟨k, hkH, hk⟩ := hS.exists_mem_conj hT'
  have h1 : k⁻¹ * q * k ∈ zpowers f := (hk q).1 (hqT' (mem_zpowers q))
  obtain ⟨n, hn⟩ := mem_zpowers_iff.1 h1
  have hkf : Commute k f := hfc k hkH
  have hx : q = f ^ n := by
    have : q = k * (k⁻¹ * q * k) * k⁻¹ := by group
    rw [this, ← hn]
    calc k * f ^ n * k⁻¹ = f ^ n * k * k⁻¹ := by rw [(hkf.zpow_right n).eq]
      _ = f ^ n := by group
  rw [hx]
  exact zpow_mem_zpowers f n

variable [Finite G] {x y : G} {K T V W : Subgroup G} {f z : G}

namespace Env37

variable (E : Env37 x y K T V W f z)

include E

theorem hx2 : x * x = 1 := by
  have := pow_orderOf_eq_one x
  rwa [E.cfg.hx2, sq] at this

theorem hf2 : f * f = 1 := by
  have := pow_orderOf_eq_one f
  rwa [E.cfg.hf2, sq] at this

theorem hz2' : orderOf z = 2 := E.cfg.z_mem.2.1

theorem hzz : z * z = 1 := by
  have := pow_orderOf_eq_one z
  rwa [E.hz2', sq] at this

theorem hz1 : z ≠ 1 := fun h => by
  have := E.hz2'
  rw [h, orderOf_one] at this
  omega

theorem hzP : z ∈ T ⊓ K := E.cfg.z_mem.1

theorem hfT : f ∈ T := E.cfg.mem.1

theorem hxT : x ∈ T := E.cfg.x_mem_T

theorem hfP : ∀ p ∈ T ⊓ K, f * p = p * f := E.cfg.mem.2.2.1

theorem hxc : ∀ t ∈ T, t * x = x * t := fun _ ht =>
  mem_centralizer_singleton_iff.1 (E.cfg.setup.sylowT.le ht)

theorem hzc : ∀ t ∈ T, t * z = z * t := E.cfg.z_mem.2.2

theorem hfx : f * x = x * f := E.cfg.hxf.symm

theorem hfz : f * z = z * f := E.cfg.z_mem.2.2 f E.hfT

theorem hfne : f ≠ x := E.cfg.mem.2.2.2.1

theorem hzx : z * x = x * z := E.hxc z E.hzP.1

theorem hCx : T ≤ centralizer ({x} : Set G) := E.cfg.setup.sylowT.le

theorem hfout : Back.actHom E.hKN ⟨f, E.hfC⟩ ∉ IVK.innAut (kBar K) :=
  not_mem_innAut_of_isFAutL2A7 E.hfFaut

theorem Q_le : T ⊓ CxK x K ≤ zpowers x := by
  intro q hq
  have hq2 : ∃ k : ℕ, q ^ (2 ^ k) = 1 := by
    obtain ⟨k, hk⟩ := E.cfg.setup.sylowT.isPGroup ⟨q, hq.1⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  exact mem_zpowers_of_two_element E.hxS (fun h hh => mem_centralizer_singleton_iff.1 hh.1) hq.2 hq2


theorem cent_P_le {d : G} (hdT : d ∈ T) (hdP : ∀ p ∈ T ⊓ K, d * p = p * d) :
    d ∈ zpowers z ⊔ zpowers f ⊔ zpowers x := by
  have hd2 : ∃ k : ℕ, d ^ (2 ^ k) = 1 := by
    obtain ⟨k, hk⟩ := E.cfg.setup.sylowT.isPGroup ⟨d, hdT⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  obtain ⟨z₀, hz₀P, hz₀2, hz₀c, a, b, hab⟩ :=
    exists_mul_mem_cmk_of_centralizes' (C := centralizer ({x} : Set G)) E.cfg.hKx E.hKN E.hPK
      E.hcen E.hAutC E.hdih E.hfC E.cfg.hf2 E.hfP E.hfout (E.hCx hdT) hd2 hdP
  have hz₀ : z₀ = z := by
    rcases E.hzu z₀ hz₀P hz₀c with h | h
    · rw [h, orderOf_one] at hz₀2
      omega
    · exact h
  subst hz₀
  have hmemT : d * z₀ ^ a * f ^ b ∈ T :=
    T.mul_mem (T.mul_mem hdT (T.zpow_mem hz₀P.1 a)) (T.zpow_mem E.hfT b)
  have hx : d * z₀ ^ a * f ^ b ∈ zpowers x := E.Q_le ⟨hmemT, hab⟩
  obtain ⟨c, hc⟩ := mem_zpowers_iff.1 hx
  have hd : d = x ^ c * f ^ (-b) * z₀ ^ (-a) := by
    rw [hc]
    group
  rw [hd]
  exact (zpowers z₀ ⊔ zpowers f ⊔ zpowers x).mul_mem
    ((zpowers z₀ ⊔ zpowers f ⊔ zpowers x).mul_mem
      (Subgroup.mem_sup_right (zpow_mem_zpowers x c))
      (Subgroup.mem_sup_left (Subgroup.mem_sup_right (zpow_mem_zpowers f _))))
    (Subgroup.mem_sup_left (Subgroup.mem_sup_left (zpow_mem_zpowers z₀ _)))

theorem coreConcl : CoreConcl (Back.actHom E.hKN) (T.subgroupOf (centralizer ({x} : Set G)))
    ((T ⊓ K).subgroupOf (centralizer ({x} : Set G))) := by
  obtain ⟨E₁, hE₁T, hE₁, hE₁16⟩ := E.hE₁
  exact core_lift_G E.cfg.hKx E.hKN E.cfg.setup.sylowT E.hcen E.hAut hE₁T hE₁ hE₁16 E.hQ2

theorem actHom_x : Back.actHom E.hKN ⟨x, (mem_centralizer_singleton_iff.2 rfl)⟩ = 1 := by
  refine (Back.actHom_eq_one_iff_commutator_mem E.hKN _).2 (fun k hk => ?_)
  have hxk : x * k = k * x := (mem_centralizer_singleton_iff.1 (E.cfg.hKx hk)).symm
  have : ⁅k, x⁆ = 1 := by
    rw [commutatorElement_def, ← hxk]
    group
  rw [this]
  exact (pPrimeCoreOf 2 K).one_mem

theorem actHom_z : ∀ hzC : z ∈ centralizer ({x} : Set G),
    Back.actHom E.hKN ⟨z, hzC⟩ ∈ IVK.innAut (kBar K) := fun hzC => by
  rw [Back.actHom_of_mem E.hKN E.hzP.2 hzC]
  exact ⟨_, rfl⟩

theorem isFMember_of_outer {g : G} (hgT : g ∈ T) (hg2 : orderOf g = 2)
    (hgP : ∀ p ∈ T ⊓ K, g * p = p * g)
    (hgout : ∀ hgC : g ∈ centralizer ({x} : Set G), Back.actHom E.hKN ⟨g, hgC⟩ ∉ IVK.innAut (kBar K)) :
    IsFMember x K T g := by
  have hgC : g ∈ centralizer ({x} : Set G) := E.hCx hgT
  have hgx : g ≠ x := by
    intro h
    apply hgout hgC
    have : (⟨g, hgC⟩ : ↥(centralizer ({x} : Set G))) = ⟨x, (mem_centralizer_singleton_iff.2 rfl)⟩ :=
      Subtype.ext h
    rw [this, E.actHom_x]
    exact (IVK.innAut (kBar K)).one_mem
  have hP' : ∀ p ∈ (T ⊓ K).subgroupOf (centralizer ({x} : Set G)),
      (⟨g, hgC⟩ : ↥(centralizer ({x} : Set G))) * p = p * ⟨g, hgC⟩ :=
    fun p hp => Subtype.ext (hgP p hp)
  obtain ⟨f₀, z₀, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hgood⟩ := E.coreConcl
  have hg2' : orderOf (⟨g, hgC⟩ : ↥(centralizer ({x} : Set G))) = 2 := by
    rw [Subgroup.orderOf_mk]; exact hg2
  rcases hgood ⟨g, hgC⟩ hgT hg2' hP' (hgout hgC) with hG | ⟨hA7, -⟩
  · exact ⟨hgT, hg2, hgP, hgx, Thm1.layer_ne_bot_of_good E.hKN hgC hg2 hG⟩
  · exact absurd hA7 E.hnotA7


theorem actHom_klein : ∀ w ∈ zpowers z ⊔ zpowers x, ∀ hwC : w ∈ centralizer ({x} : Set G),
    Back.actHom E.hKN ⟨w, hwC⟩ ∈ IVK.innAut (kBar K) := by
  intro w hw hwC
  have hzC : z ∈ centralizer ({x} : Set G) := E.hCx E.hzP.1
  have hxC : x ∈ centralizer ({x} : Set G) := mem_centralizer_singleton_iff.2 rfl
  rcases Thm1G33.klein_cases E.hzz E.hx2 E.hzx hw with h | h | h | h
  · have : (⟨w, hwC⟩ : ↥(centralizer ({x} : Set G))) = 1 := Subtype.ext h
    rw [this, map_one]
    exact (IVK.innAut (kBar K)).one_mem
  · have : (⟨w, hwC⟩ : ↥(centralizer ({x} : Set G))) = ⟨z, hzC⟩ := Subtype.ext h
    rw [this]
    exact E.actHom_z hzC
  · have : (⟨w, hwC⟩ : ↥(centralizer ({x} : Set G))) = ⟨x, hxC⟩ := Subtype.ext h
    rw [this, E.actHom_x]
    exact (IVK.innAut (kBar K)).one_mem
  · have : (⟨w, hwC⟩ : ↥(centralizer ({x} : Set G))) = ⟨z, hzC⟩ * ⟨x, hxC⟩ := Subtype.ext h
    rw [this, map_mul, E.actHom_x, mul_one]
    exact E.actHom_z hzC

theorem actHom_f_mul_outer : ∀ w ∈ zpowers z ⊔ zpowers x, ∀ hgC : f * w ∈ centralizer ({x} : Set G),
    Back.actHom E.hKN ⟨f * w, hgC⟩ ∉ IVK.innAut (kBar K) := by
  intro w hw hgC' hin
  have hwT : w ∈ T := (sup_le (zpowers_le.2 E.hzP.1) (zpowers_le.2 E.hxT)) hw
  apply E.hfout
  have hwC : w ∈ centralizer ({x} : Set G) := E.hCx hwT
  have h1 : (⟨f * w, hgC'⟩ : ↥(centralizer ({x} : Set G))) = ⟨f, E.hfC⟩ * ⟨w, hwC⟩ := rfl
  rw [h1, map_mul] at hin
  have := (IVK.innAut (kBar K)).mul_mem hin ((IVK.innAut (kBar K)).inv_mem (E.actHom_klein w hw hwC))
  simpa using this

theorem isFMember_f_mul : ∀ w ∈ zpowers z ⊔ zpowers x, IsFMember x K T (f * w) := by
  intro w hw
  have hwT : w ∈ T := (sup_le (zpowers_le.2 E.hzP.1) (zpowers_le.2 E.hxT)) hw
  have hwP : ∀ p ∈ T ⊓ K, w * p = p * w := by
    intro p hp
    have hle : zpowers z ⊔ zpowers x ≤ centralizer ({p} : Set G) := by
      refine sup_le (zpowers_le.2 ?_) (zpowers_le.2 ?_)
      · exact mem_centralizer_singleton_iff.2 (E.hzc p hp.1).symm
      · exact mem_centralizer_singleton_iff.2 (E.hxc p hp.1).symm
    exact mem_centralizer_singleton_iff.1 (hle hw)
  have hwf : f * w = w * f := by
    have hle : zpowers z ⊔ zpowers x ≤ centralizer ({f} : Set G) := by
      refine sup_le (zpowers_le.2 ?_) (zpowers_le.2 ?_)
      · exact mem_centralizer_singleton_iff.2 E.hfz.symm
      · exact mem_centralizer_singleton_iff.2 E.hfx.symm
    exact (mem_centralizer_singleton_iff.1 (hle hw)).symm
  have hww : w * w = 1 := by
    rcases Thm1G33.klein_cases E.hzz E.hx2 E.hzx hw with h | h | h | h
    · rw [h]; simp
    · rw [h]; exact E.hzz
    · rw [h]; exact E.hx2
    · rw [h]
      calc z * x * (z * x) = (z * z) * (x * x) := by
            calc z * x * (z * x) = z * (x * z) * x := by group
              _ = z * (z * x) * x := by rw [← E.hzx]
              _ = (z * z) * (x * x) := by group
        _ = 1 := by rw [E.hzz, E.hx2, one_mul]
  have hgC : f * w ∈ centralizer ({x} : Set G) := E.hCx (T.mul_mem E.hfT hwT)
  have hout := E.actHom_f_mul_outer w hw
  have hne1 : f * w ≠ 1 := by
    intro h
    apply hout hgC
    have : (⟨f * w, hgC⟩ : ↥(centralizer ({x} : Set G))) = 1 := Subtype.ext h
    rw [this, map_one]
    exact (IVK.innAut (kBar K)).one_mem
  have hg2 : orderOf (f * w) = 2 := by
    refine orderOf_eq_prime ?_ hne1
    calc (f * w) ^ 2 = f * w * (f * w) := sq _
      _ = f * (w * f) * w := by group
      _ = f * (f * w) * w := by rw [← hwf]
      _ = (f * f) * (w * w) := by group
      _ = 1 := by rw [E.hf2, hww, one_mul]
  refine E.isFMember_of_outer (T.mul_mem E.hfT hwT) hg2 ?_ hout
  intro p hp
  calc f * w * p = f * (w * p) := by group
    _ = f * (p * w) := by rw [hwP p hp]
    _ = f * p * w := by group
    _ = p * f * w := by rw [E.hfP p hp]
    _ = p * (f * w) := by group

theorem fmax2_of_mem {g : G} (hg : IsFMember x K T g) : FMax2 x y K g :=
  ⟨⟨⟨E.cfg.hu2, T, E.cfg.setup, hg⟩, E.cfg.fmax.1.1.2⟩, E.cfg.fmax.1.2⟩

theorem bound (hle : Nat.card ↥V ≤ Nat.card ↥T) {g : G} (hg : IsFMember x K T g) :
    twoPartCard (centralizer ({g} : Set G)) ≤ Nat.card ↥T := by
  have h1 := E.cfg.fmax.2 x y K g (E.fmax2_of_mem hg)
  have h2 : twoPartCard (centralizer ({f} : Set G)) = Nat.card ↥V := E.cfg.sylowV.card_eq.symm
  omega

theorem actHom_inner_of_mem_P : ∀ p ∈ T ⊓ K, ∀ hpC : p ∈ centralizer ({x} : Set G),
    Back.actHom E.hKN ⟨p, hpC⟩ ∈ IVK.innAut (kBar K) := fun p hp hpC => by
  rw [Back.actHom_of_mem E.hKN hp.2 hpC]
  exact ⟨_, rfl⟩

theorem actHom_conj_outer {g u : G} (hgC : g ∈ centralizer ({x} : Set G))
    (huC : u ∈ centralizer ({x} : Set G))
    (hu : Back.actHom E.hKN ⟨u, huC⟩ ∉ IVK.innAut (kBar K)) :
    ∀ hC : g * u * g⁻¹ ∈ centralizer ({x} : Set G),
      Back.actHom E.hKN ⟨g * u * g⁻¹, hC⟩ ∉ IVK.innAut (kBar K) := by
  intro hC hin
  apply hu
  have h1 : (⟨g * u * g⁻¹, hC⟩ : ↥(centralizer ({x} : Set G))) =
      ⟨g, hgC⟩ * ⟨u, huC⟩ * ⟨g, hgC⟩⁻¹ := rfl
  rw [h1, map_mul, map_mul, map_inv] at hin
  have := Subgroup.Normal.conj_mem (IVK.innAut_normal (K := kBar K)) _ hin
    (Back.actHom E.hKN ⟨g, hgC⟩)⁻¹
  simpa [mul_assoc] using this

theorem fusion' : ∀ u ∈ T ⊓ K ⊔ zpowers f, orderOf u = 2 →
    ∃ g ∈ K ⊔ zpowers f, g * u * g⁻¹ = z ∨ g * u * g⁻¹ = f ∨ g * u * g⁻¹ = f * z := by
  obtain ⟨E₁, hE₁T, hE₁, hE₁16⟩ := E.hE₁
  exact transport_fusion_G' E.cfg.hKx E.hKN E.cfg.setup.sylowT E.hcen E.hAut hE₁T hE₁ hE₁16 E.hQ2
    E.hfT E.cfg.hf2 E.hfP (fun _ => E.hfout) E.hzP E.hz2' (fun p hp => (E.hzc p hp.1).symm)

end Env37

end CFSG.GH74.GLS.C3.Layer1.Thm1P38
