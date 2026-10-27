module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.E3U0
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.E3Rank
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.NotStandardInputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.M22Engine
public import Certificates.Certificate24784
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.E3Lift

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.EvenSporadicStandard.M23Std

theorem eight_dvd_card_centralizer_of_sq {A : Type*} [Group A]
    (e : A ≃* alternatingGroup (Fin 6)) {a : A} (ha : a * a = 1) :
    8 ∣ Nat.card (centralizer ({a} : Set A)) := by
  have h := of_decide_eq_true (Certificates.certificate24784 : a6CentCheck = true)
  have h1 := h (e a) (by rw [← map_mul, ha, map_one])
  have : Nat.card (centralizer ({a} : Set A)) =
      Fintype.card {b : alternatingGroup (Fin 6) // e a * b = b * e a} := by
    rw [← Nat.card_eq_fintype_card]
    refine Nat.card_congr ?_
    refine (Equiv.subtypeEquivRight (fun b => mem_centralizer_singleton_iff)).trans ?_
    refine Equiv.subtypeEquiv e.toEquiv (fun b => ?_)
    constructor
    · intro hb
      have := congrArg e hb
      rw [map_mul, map_mul] at this
      exact this.symm
    · intro hb
      apply e.injective
      rw [map_mul, map_mul]
      exact hb.symm
  rw [this]
  exact h1

theorem fin76aWreathNoFusionM22 :
    Fin76aWreathNoFusionM22 := by
  intro G _ _ L h hL z t F L1 N hz hz2 hC S hnc hA6 N1 N2 he1 he2 hcomm hdisj hnorm hidx hz0 hconj
    g hmem
  obtain ⟨e1⟩ := he1
  obtain ⟨e2⟩ := he2
  have := h.simple
  have hzz : z * z = 1 := S.one.z_mul_self
  set y : G := g⁻¹ * z * g with hy
  have hy2 : y * y = 1 := by
    calc y * y = g⁻¹ * (z * z) * g := by rw [hy]; group
      _ = 1 := by rw [hzz]; group
  have hconjy : IsConj z y := isConj_iff.2 ⟨g⁻¹, by rw [hy]; group⟩
  obtain ⟨hyX, hρy⟩ := mem_preimageY.1 hmem
  have hR := m22_rankFour hL
  obtain ⟨Cy, hCymem, hCycard, hH⟩ := card_centralizer_L1 S hR hnc hyX hy2 hconjy
  set X : Subgroup G := normalizer (L1 : Set G) with hX
  set yX : ↥X := ⟨y, hyX⟩ with hyXdef
  have hN2c : N2 ≤ centralizer (N1 : Set (Ybar L1)) := fun b hb =>
    mem_centralizer_iff.2 fun a ha => hcomm a ha b hb
  obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_of_mem_sup_of_le_centralizer hN2c hρy
  have hρy2 : (piY L1) yX * (piY L1) yX = 1 := by
    rw [← map_mul]
    have : yX * yX = 1 := Subtype.ext hy2
    rw [this, map_one]
  have hab2 : (a * b) * (a * b) = 1 := by rw [← hab]; exact hρy2
  have hab' : (a * b) * (a * b) = (a * a) * (b * b) := by
    calc (a * b) * (a * b) = a * (b * a) * b := by simp only [mul_assoc]
      _ = a * (a * b) * b := by rw [← hcomm a ha b hb]
      _ = (a * a) * (b * b) := by simp only [mul_assoc]
  have haa : a * a = 1 := by
    have h1 : a * a = (b * b)⁻¹ := eq_inv_of_mul_eq_one_left (hab'.symm.trans hab2)
    have h2 : a * a ∈ N1 := Subgroup.mul_mem _ ha ha
    have h3 : a * a ∈ N2 := by rw [h1]; exact Subgroup.inv_mem _ (Subgroup.mul_mem _ hb hb)
    exact Subgroup.disjoint_def.1 hdisj h2 h3
  have hbb : b * b = 1 := by
    have := hab'.symm.trans hab2
    rwa [haa, one_mul] at this
  set a' : ↥N1 := ⟨a, ha⟩ with ha'
  set b' : ↥N2 := ⟨b, hb⟩ with hb'
  have ha'2 : a' * a' = 1 := Subtype.ext haa
  have hb'2 : b' * b' = 1 := Subtype.ext hbb
  set C1 : Subgroup (Ybar L1) := (centralizer ({a'} : Set ↥N1)).map N1.subtype with hC1
  set C2 : Subgroup (Ybar L1) := (centralizer ({b'} : Set ↥N2)).map N2.subtype with hC2
  have hC1card : 8 ∣ Nat.card C1 := by
    rw [hC1, Subgroup.card_map_of_injective N1.subtype_injective]
    exact eight_dvd_card_centralizer_of_sq e1 ha'2
  have hC2card : 8 ∣ Nat.card C2 := by
    rw [hC2, Subgroup.card_map_of_injective N2.subtype_injective]
    exact eight_dvd_card_centralizer_of_sq e2 hb'2
  have hC1N : C1 ≤ N1 := by
    rintro _ ⟨c, -, rfl⟩
    exact c.2
  have hC2N : C2 ≤ N2 := by
    rintro _ ⟨c, -, rfl⟩
    exact c.2
  have hC2C1 : C2 ≤ centralizer (C1 : Set (Ybar L1)) := fun c2 hc2 =>
    mem_centralizer_iff.2 fun c1 hc1 => hcomm c1 (hC1N hc1) c2 (hC2N hc2)
  have hC12disj : Disjoint C1 C2 := hdisj.mono hC1N hC2N
  set Q : Subgroup (Ybar L1) := C1 ⊔ C2 with hQ
  have hQcard : Nat.card Q = Nat.card C1 * Nat.card C2 := by
    rw [hQ, ← Nat.card_congr (mulEquivProdSup hC2C1 hC12disj).toEquiv, Nat.card_prod]
  have hQ64 : 64 ∣ Nat.card Q := by
    rw [hQcard]
    obtain ⟨k1, hk1⟩ := hC1card
    obtain ⟨k2, hk2⟩ := hC2card
    exact ⟨k1 * k2, by rw [hk1, hk2]; ring⟩
  have hQc : ∀ q ∈ Q, q * (piY L1) yX = (piY L1) yX * q := by
    intro q hq
    obtain ⟨c1, hc1, c2, hc2, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer hC2C1 hq
    have h1 : c1 * a = a * c1 := by
      obtain ⟨c, hc, rfl⟩ := hc1
      have := mem_centralizer_singleton_iff.1 hc
      exact congrArg Subtype.val this
    have h1' : c1 * b = b * c1 := hcomm c1 (hC1N hc1) b hb
    have h2 : c2 * b = b * c2 := by
      obtain ⟨c, hc, rfl⟩ := hc2
      have := mem_centralizer_singleton_iff.1 hc
      exact congrArg Subtype.val this
    have h2' : c2 * a = a * c2 := (hcomm a ha c2 (hC2N hc2)).symm
    rw [hab]
    calc c1 * c2 * (a * b) = c1 * (c2 * a) * b := by simp only [mul_assoc]
      _ = c1 * (a * c2) * b := by rw [h2']
      _ = (c1 * a) * (c2 * b) := by simp only [mul_assoc]
      _ = (a * c1) * (b * c2) := by rw [h1, h2]
      _ = a * (c1 * b) * c2 := by simp only [mul_assoc]
      _ = a * (b * c1) * c2 := by rw [h1']
      _ = a * b * (c1 * c2) := by simp only [mul_assoc]
  set H' : Subgroup ↥X := centralizer ({yX} : Set ↥X) ⊓ Q.comap (piY L1) with hH'
  set ψ : ↥H' →* Ybar L1 := (piY L1).comp H'.subtype with hψ
  have hX_mem : ∀ {u : G}, u ∈ U0 L1 → u ∈ X := fun hu => U0_le_X L1 hu
  have hψrange : ψ.range = Q := by
    apply le_antisymm
    · rintro _ ⟨h', rfl⟩
      exact (Subgroup.mem_inf.1 h'.2).2
    · intro q hq
      obtain ⟨x, hx⟩ := piY_surjective L1 q
      have hcx : (piY L1) x * (piY L1) yX = (piY L1) yX * (piY L1) x := by rw [hx]; exact hQc q hq
      have hxyX : (x : G) * y * (x : G)⁻¹ * y⁻¹ ∈ X :=
        X.mul_mem (X.mul_mem (X.mul_mem x.2 hyX) (X.inv_mem x.2)) (X.inv_mem hyX)
      have hmemU : (x : G) * y * (x : G)⁻¹ * y⁻¹ ∈ U0 L1 := by
        refine mem_U0.2 ⟨hxyX, ?_⟩
        have e : (⟨(x : G) * y * (x : G)⁻¹ * y⁻¹, hxyX⟩ : ↥X) = x * yX * x⁻¹ * yX⁻¹ := rfl
        rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, hcx]
        group
      obtain ⟨u, hu, hcen⟩ := exists_mem_centralizer_of_conj_mem_lift (X := X) (U₀ := U0 L1)
        (L₁ := L1) (U0_le_X L1) (fun x hx u hu => U0_norm hx hu) (Setup.L1_le_U0 S) S.isPGroup_L1
        (Setup.not_two_dvd_relIndex_U0 S)
        (fun x hx l hl => (Subgroup.mem_normalizer_iff.1 hx l).1 hl)
        S.L1_sq hyX hy2 hH hmemU
      have hu_inv : u⁻¹ ∈ U0 L1 := Subgroup.inv_mem _ hu
      have hx'X : u⁻¹ * (x : G) ∈ X := X.mul_mem (X.inv_mem (hX_mem hu)) x.2
      set x' : ↥X := ⟨u⁻¹ * (x : G), hx'X⟩ with hx'
      have hρx' : (piY L1) x' = q := by
        have e : x' = ⟨u⁻¹, hX_mem hu_inv⟩ * x := rfl
        rw [e, map_mul, (mem_U0.1 hu_inv).2, one_mul]
        exact hx
      have hcx' : x' ∈ centralizer ({yX} : Set ↥X) := by
        refine mem_centralizer_iff.2 fun h hh => ?_
        rw [Set.mem_singleton_iff] at hh
        subst hh
        apply Subtype.ext
        exact (mul_inv_eq_iff_eq_mul.1 hcen).symm
      exact ⟨⟨x', Subgroup.mem_inf.2 ⟨hcx', by rw [Subgroup.mem_comap, hρx']; exact hq⟩⟩, hρx'⟩
  set f : ↥H' →* G := X.subtype.comp H'.subtype with hf
  have hfinj : Function.Injective f := X.subtype_injective.comp H'.subtype_injective
  have hCy : Cy ≤ (ψ.ker).map f := by
    intro c hc
    obtain ⟨hcL, hcy⟩ := (hCymem c).1 hc
    have hcX : c ∈ X := Subgroup.le_normalizer hcL
    have hcU : c ∈ U0 L1 := Setup.L1_le_U0 S hcL
    have hcen : (⟨c, hcX⟩ : ↥X) ∈ centralizer ({yX} : Set ↥X) := by
      refine mem_centralizer_iff.2 fun h hh => ?_
      rw [Set.mem_singleton_iff] at hh
      subst hh
      apply Subtype.ext
      show y * c = c * y
      calc y * c = (y * c * y⁻¹) * y := by group
        _ = c * y := by rw [hcy]
    have hρc : (piY L1) ⟨c, hcX⟩ = 1 := (mem_U0.1 hcU).2
    have hmem' : (⟨c, hcX⟩ : ↥X) ∈ H' :=
      Subgroup.mem_inf.2 ⟨hcen, by rw [Subgroup.mem_comap, hρc]; exact Q.one_mem⟩
    exact ⟨⟨⟨c, hcX⟩, hmem'⟩, MonoidHom.mem_ker.2 hρc, rfl⟩
  have h16 : 16 ∣ Nat.card ψ.ker := by
    have h1 := Subgroup.card_dvd_of_le hCy
    rw [Subgroup.card_map_of_injective hfinj, hCycard] at h1
    exact h1
  have hH'card : Nat.card ψ.ker * Nat.card Q = Nat.card H' := by
    have := Subgroup.card_ker_mul_card_range ψ
    rwa [hψrange] at this
  have h1024 : 1024 ∣ Nat.card H' := by
    rw [← hH'card]
    obtain ⟨k1, hk1⟩ := h16
    obtain ⟨k2, hk2⟩ := hQ64
    exact ⟨k1 * k2, by rw [hk1, hk2]; ring⟩
  set f' : ↥H' →* G := (MulAut.conj g).toMonoidHom.comp f with hf'
  have hf'inj : Function.Injective f' := (MulAut.conj g).injective.comp hfinj
  have hf'range : f'.range ≤ centralizer ({z} : Set G) := by
    rintro _ ⟨k, rfl⟩
    have hk := (Subgroup.mem_inf.1 k.2).1
    have hk' := mem_centralizer_iff.1 hk yX rfl
    have hky : y * (k : ↥X) = (k : ↥X) * y := congrArg Subtype.val hk'
    show g * (k : G) * g⁻¹ ∈ centralizer ({z} : Set G)
    rw [mem_centralizer_singleton_iff]
    calc g * (k : G) * g⁻¹ * z = g * (k * (g⁻¹ * z * g)) * g⁻¹ := by group
      _ = g * (k * y) * g⁻¹ := by rw [hy]
      _ = g * (y * k) * g⁻¹ := by rw [hky]
      _ = z * (g * (k : G) * g⁻¹) := by rw [hy]; group
  have hdvd : Nat.card H' ∣ Nat.card (centralizer ({z} : Set G)) := by
    have h1 := Subgroup.card_dvd_of_le hf'range
    rwa [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hf'inj, Subgroup.card_top] at h1
  have hCz : Nat.card (centralizer ({z} : Set G)) = 443520 * 2 := by
    rw [centralizer_z_eq S.one, card_sup_zpowers S.one (le_refl L)]
    obtain ⟨eL⟩ := hL
    have hM : Nat.card (Carrier .M22) = 443520 := CFSG.Sporadic.Mathieu.card_M22
    rw [Nat.card_congr eL.toEquiv, hM]
  rw [hCz] at hdvd
  have := dvd_trans h1024 hdvd
  omega

end CFSG.EvenSporadicStandard.M22Std
