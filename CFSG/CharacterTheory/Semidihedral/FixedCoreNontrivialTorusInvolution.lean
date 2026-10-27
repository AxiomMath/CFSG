module

public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialTorusDihedral
public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialSetup

public section

namespace CFSG.Semidihedral.FixedCoreNontrivial

open CFSG.GorensteinWalter

variable {G : Type} [Group G] {t s d : G} {J B W : Subgroup G}

theorem LocalData.torus_involutions [Finite G] (hL : LocalData t s d J B W)
    (hWodd : Odd (Nat.card W)) (hBodd : Odd (Nat.card B)) (hW1 : W ≠ ⊥) (hBne : B ≠ ⊥)
    {g : G} (hgt : g * t * g⁻¹ = s) (hgW : g ∈ Subgroup.centralizer (W : Set G))
    (hVK : Subgroup.zpowers t ⊔ Subgroup.zpowers s ≤ Subgroup.centralizer (W : Set G))
    (hKH2 : (Subgroup.centralizer (W : Set G)).relIndex (Subgroup.normalizer (W : Set G)) = 2)
    (hinvH : ∀ h ∈ Subgroup.normalizer (W : Set G), h ∉ Subgroup.centralizer (W : Set G) →
      ∀ w ∈ W, h * w * h⁻¹ = w⁻¹)
    (hdK : d ∉ Subgroup.centralizer (W : Set G))
    (hOH : (CFSG.pPrimeCore 2 (Subgroup.normalizer (W : Set G))).map
      (Subgroup.normalizer (W : Set G)).subtype = W)
    (F' : Type) [Field F'] [Finite F']
    (φ : Subgroup.normalizer (W : Set G) ⧸ CFSG.pPrimeCore 2 (Subgroup.normalizer (W : Set G)) ≃*
      PGL2 F')
    (hF' : IsOddPrimePower (Nat.card F')) (hmod : Nat.card F' % 8 = 3 ∨ Nat.card F' % 8 = 5)
    (hpsl : 3 < Nat.card F' →
      (((Subgroup.centralizer (W : Set G)).subgroupOf (Subgroup.normalizer (W : Set G))).map
        (QuotientGroup.mk' (CFSG.pPrimeCore 2 (Subgroup.normalizer (W : Set G))))).map
          φ.toMonoidHom =
        (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F')).range) :
    let H : Subgroup G := Subgroup.normalizer (W : Set G)
    let K : Subgroup G := Subgroup.centralizer (W : Set G)
    let q' : ℕ := Nat.card F'
    let e' : ℤ := if q' % 4 = 1 then 1 else -1
    let v : G := s * d
    let X : Subgroup G := H ⊓ Subgroup.centralizer {v}
    let U : Subgroup G := (CFSG.pPrimeCore 2 X).map X.subtype
    3 < q' ∧ 4 * (Nat.card B : ℤ) = q' - e' ∧
      orderOf v = 2 ∧ v ∈ H ∧ v ∉ K ∧ IsCyclic U ∧ 2 * (Nat.card U : ℤ) = q' + e' ∧
      U ≤ K ∧ (∀ u ∈ U, t * u * t⁻¹ = u⁻¹) ∧ Nat.Coprime (Nat.card U) (Nat.card B) := by
  intro H K q' e' v X U
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKH : K ≤ H := Subgroup.centralizer_le_normalizer _
  have hWK : W ≤ K := fun w hw =>
    Subgroup.mem_centralizer_iff.mpr fun y hy => hL.W_comm y hy w hw
  have htK : t ∈ K := hVK (Subgroup.mem_sup_left (Subgroup.mem_zpowers t))
  have hsK : s ∈ K := hVK (Subgroup.mem_sup_right (Subgroup.mem_zpowers s))
  have hdH : d ∈ H := hL.d_mem_normalizer W le_rfl
  have htH : t ∈ H := hKH htK
  have hsH : s ∈ H := hKH hsK
  have hgH : g ∈ H := hKH hgW
  have hCH := hL.centralizer_inf_normalizer_eq W le_rfl hW1
  have hCHcard : Nat.card (Subgroup.centralizer ({t} : Set G) ⊓ H : Subgroup G) =
      8 * (Nat.card W * Nat.card B) := by
    rw [hCH]
    exact hL.card_sup_dihedral hWodd hBodd
  set O : Subgroup H := CFSG.pPrimeCore 2 H with hOdef
  have hOcard : Nat.card O = Nat.card W := by
    rw [← hOH]
    exact (Subgroup.card_map_of_injective H.subtype_injective).symm
  have hOodd : Odd (Nat.card O) := hOcard ▸ hWodd
  have hHcard : Nat.card H = q' * (q' ^ 2 - 1) * Nat.card W := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup O, Nat.card_congr φ.toEquiv,
      pgl2_card_formula, hOcard]
  have hOW : ∀ o ∈ O, (o : G) ∈ W := fun o ho => hOH ▸ ⟨o, ho, rfl⟩
  have hW0 : 0 < Nat.card W := Nat.card_pos
  have hq'3 : 3 < q' := by
    obtain ⟨p, k, hp, hpodd, hk, hq⟩ := hF'
    have hp3 : 3 ≤ p := by
      rcases hpodd with ⟨r, hr⟩
      have := hp.two_le
      omega
    have hq3 : 3 ≤ q' := by
      show 3 ≤ Nat.card F'
      rw [hq]
      exact hp3.trans (Nat.le_self_pow (by omega) p)
    rcases Nat.lt_or_ge 3 q' with h | h
    · exact h
    · exfalso
      have hq3' : q' = 3 := by omega
      have hdvd := Subgroup.card_dvd_of_le (inf_le_right :
        Subgroup.centralizer ({t} : Set G) ⊓ H ≤ H)
      rw [hCHcard, hHcard, hq3'] at hdvd
      have hB3 : Nat.card B ∣ 3 := by
        have h8 : 8 * Nat.card W * Nat.card B ∣ 8 * Nat.card W * 3 := by
          have e1 : 8 * (Nat.card W * Nat.card B) = 8 * Nat.card W * Nat.card B := by ring
          have e2 : 3 * (3 ^ 2 - 1) * Nat.card W = 8 * Nat.card W * 3 := by norm_num; ring
          rw [← e1, ← e2]
          exact hdvd
        exact Nat.dvd_of_mul_dvd_mul_left (by positivity) h8
      have hB1 : Nat.card B ≠ 1 := fun h1 => hBne (Subgroup.card_eq_one.mp h1)
      have hBeq : Nat.card B = 3 := by
        rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hB3 with h | h
        · exact absurd h hB1
        · exact h
      have heq : Subgroup.centralizer ({t} : Set G) ⊓ H = H :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by
          rw [hCHcard, hHcard, hq3', hBeq]
          norm_num
          ring_nf
          exact le_refl _)
      have hgC : g ∈ Subgroup.centralizer ({t} : Set G) ⊓ H := by rw [heq]; exact hgH
      have hgt' : g * t = t * g := Subgroup.mem_centralizer_singleton_iff.mp hgC.1
      apply hL.s_ne
      rw [← hgt, hgt']
      group
  set π : H →* H ⧸ O := QuotientGroup.mk' O with hπdef
  set t' : H := ⟨t, htH⟩ with ht'def
  have ht'2 : t' * t' = 1 := Subtype.ext hL.t_sq
  have hCt : (Subgroup.centralizer ({t'} : Set H)).map H.subtype =
      Subgroup.centralizer ({t} : Set G) ⊓ H := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_, y.2⟩
      exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hy)
    · rintro ⟨hx1, hx2⟩
      refine ⟨⟨x, hx2⟩, Subgroup.mem_centralizer_singleton_iff.mpr ?_, rfl⟩
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hx1)
  have hCtcard : Nat.card (Subgroup.centralizer ({t'} : Set H)) =
      8 * (Nat.card W * Nat.card B) := by
    rw [← hCHcard, ← hCt, Subgroup.card_map_of_injective H.subtype_injective]
  have hOCt : O ≤ Subgroup.centralizer ({t'} : Set H) := by
    intro o ho
    refine Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext ?_)
    exact (hL.t_comm_W o (hOW o ho)).symm
  have hmapcard : Nat.card ((Subgroup.centralizer ({t'} : Set H)).map π) =
      8 * Nat.card B := by
    have h1 := card_map_mk_mul O (Subgroup.centralizer ({t'} : Set H))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOCt).toEquiv, hOcard, hCtcard] at h1
    have h2 : Nat.card ((Subgroup.centralizer ({t'} : Set H)).map π) * Nat.card W =
        (8 * Nat.card B) * Nat.card W := by rw [h1]; ring
    exact Nat.eq_of_mul_eq_mul_right hW0 h2
  rw [centralizer_map_mk hOodd ht'2] at hmapcard
  have hxt : Nat.card (Subgroup.centralizer ({φ (π t')} : Set (PGL2 F'))) = 8 * Nat.card B := by
    rw [← map_centralizer_mulEquiv, Subgroup.card_map_of_injective φ.injective]
    exact hmapcard
  have hxt2 : φ (π t') * φ (π t') = 1 := by rw [← map_mul, ← map_mul, ht'2, map_one, map_one]
  have hxt1 : φ (π t') ≠ 1 := by
    intro h1
    have h2 : π t' = 1 := φ.injective (by rw [h1, map_one])
    have h3 : t' ∈ O := (QuotientGroup.eq_one_iff t').mp h2
    exact hL.not_odd_t (hL.W_odd t (hOW t' h3))
  have hxtR : φ (π t') ∈
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F')).range := by
    rw [← hpsl hq'3]
    exact ⟨π t', ⟨t', Subgroup.mem_subgroupOf.mpr htK, rfl⟩, rfl⟩
  have hcent := card_centralizer_of_involution_mem F' hF' hq'3 hxt2 hxt1 hxtR
  rw [hxt] at hcent
  have h4B : 4 * (Nat.card B : ℤ) = q' - e' := by
    push_cast at hcent
    show 4 * (Nat.card B : ℤ) = (Nat.card F' : ℤ) - (if Nat.card F' % 4 = 1 then 1 else -1)
    linarith
  have hv2 : v * v = 1 := by
    show s * d * (s * d) = 1
    calc s * d * (s * d) = (s * d * s⁻¹) * d := by rw [hL.s_inv_eq]; group
      _ = 1 := by rw [hL.s_d_inv, inv_mul_cancel]
  have hv1 : v ≠ 1 := by
    intro h1
    apply hL.s_not_mem_J
    have h2 : s = d⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [h2]
    exact J.inv_mem hL.d_mem
  have hvo : orderOf v = 2 := orderOf_eq_prime (by rw [pow_two]; exact hv2) hv1
  have hvH : v ∈ H := H.mul_mem hsH hdH
  have hvK : v ∉ K := by
    intro h1
    apply hdK
    have h2 : d = s⁻¹ * v := by show d = s⁻¹ * (s * d); group
    rw [h2]
    exact K.mul_mem (K.inv_mem hsK) h1
  set v' : H := ⟨v, hvH⟩ with hv'def
  have hv'2 : v' * v' = 1 := Subtype.ext hv2
  set θ : H →* PGL2 F' := φ.toMonoidHom.comp π with hθdef
  have hθ : ∀ e : H, θ e = 1 ↔ e ∈ O := by
    intro e
    constructor
    · intro h1
      have h2 : π e = 1 := φ.injective (by rw [map_one]; exact h1)
      exact (QuotientGroup.eq_one_iff e).mp h2
    · intro h1
      have h2 : π e = 1 := (QuotientGroup.eq_one_iff e).mpr h1
      show φ (π e) = 1
      rw [h2, map_one]
  have hx2 : θ v' * θ v' = 1 := by rw [← map_mul, hv'2, map_one]
  have hx1 : θ v' ≠ 1 := by
    intro h1
    have h2 := hOW v' ((hθ v').mp h1)
    have h3 := hL.W_odd v h2
    rw [hvo] at h3
    exact absurd h3 (by decide)
  have hxR : θ v' ∉
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F')).range := by
    intro hx
    rw [← hpsl hq'3] at hx
    obtain ⟨y, ⟨k, hk, rfl⟩, hky⟩ := hx
    have h1 : π k = π v' := φ.injective hky
    have h2 : k⁻¹ * v' ∈ O := by
      apply (QuotientGroup.eq_one_iff _).mp
      change π (k⁻¹ * v') = 1
      rw [map_mul, map_inv, h1, inv_mul_cancel]
    apply hvK
    have h3 : (k : G) * ((k⁻¹ * v' : H) : G) = v := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
    rw [← h3]
    exact K.mul_mem (Subgroup.mem_subgroupOf.mp hk) (hWK (hOW _ h2))
  obtain ⟨U₁, w₁, hU₁c, hU₁card, hxU₁, hw₁U, hw₁2, hw₁inv, hCx⟩ :=
    centralizer_of_involution_not_mem F' hF' hq'3 hx2 hx1 hxR
  have he' : (q' % 8 = 3 → e' = -1) ∧ (q' % 8 = 5 → e' = 1) := by
    constructor
    · intro h
      show (if q' % 4 = 1 then (1 : ℤ) else -1) = -1
      simp [show ¬ q' % 4 = 1 by omega]
    · intro h
      show (if q' % 4 = 1 then (1 : ℤ) else -1) = 1
      simp [show q' % 4 = 1 by omega]
  have hU₁card' : (Nat.card U₁ : ℤ) = q' + e' := hU₁card
  obtain ⟨m, hm2, hmodd⟩ : ∃ m : ℕ, Nat.card U₁ = 2 * m ∧ Odd m := by
    rcases hmod with h | h
    · have h1 : (Nat.card U₁ : ℤ) = q' - 1 := by rw [hU₁card', he'.1 h]; ring
      refine ⟨(q' - 1) / 2, by omega, Nat.odd_iff.mpr (by omega)⟩
    · have h1 : (Nat.card U₁ : ℤ) = q' + 1 := by rw [hU₁card', he'.2 h]
      refine ⟨(q' + 1) / 2, by omega, Nat.odd_iff.mpr (by omega)⟩
  let : Finite (PGL2 F') :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  obtain ⟨hOc, hOcard', hOinv, huniq⟩ := dihedral_odd_core hU₁c hmodd hm2 hw₁2 hw₁inv hCx
  set A : Subgroup H := Subgroup.centralizer ({v'} : Set H) with hAdef
  have hAO : ∀ a ∈ A, a ∈ O → a = 1 := by
    intro a ha hao
    have haW := hOW a hao
    have h1 : v * a * v⁻¹ = a := by
      have h2 : a * v' = v' * a := Subgroup.mem_centralizer_singleton_iff.mp ha
      have h3 : (a : G) * v = v * a := congrArg Subtype.val h2
      rw [← h3]
      group
    have h2 : v * a * v⁻¹ = (a : G)⁻¹ := hinvH v hvH hvK a haW
    have h3 : (a : G) * a = 1 := by
      calc (a : G) * a = (a : G)⁻¹⁻¹ * a := by rw [inv_inv]
        _ = 1 := by rw [← h2, h1, inv_mul_cancel]
    exact Subtype.ext (eq_one_of_mul_self_eq_one_of_odd (hL.W_odd a haW) h3)
  have hinj : Set.InjOn θ A := by
    intro a ha b hb hab
    have h1 : θ (a⁻¹ * b) = 1 := by rw [map_mul, map_inv, hab, inv_mul_cancel]
    have h3 := hAO _ (A.mul_mem (A.inv_mem ha) hb) ((hθ _).mp h1)
    exact (inv_mul_eq_one.mp h3)
  have hAθ : A.map θ = Subgroup.centralizer ({θ v'} : Set (PGL2 F')) := by
    rw [hθdef, ← Subgroup.map_map, centralizer_map_mk hOodd hv'2, map_centralizer_mulEquiv]
    rfl
  set ψ : A ≃* Subgroup.centralizer ({θ v'} : Set (PGL2 F')) :=
    (mulEquivMapOfInjOn θ hinj).trans (MulEquiv.subgroupCongr hAθ) with hψdef
  have hψ : ∀ a : A, (ψ a : PGL2 F') = θ a := fun a => by
    rw [hψdef, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply, mulEquivMapOfInjOn_apply]
  have hcore := CFSG.pPrimeCore_map_iso 2 ψ
  have hXA : A.map H.subtype = X := by
    ext y
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine ⟨a.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp ha)
    · rintro ⟨hyH, hyv⟩
      refine ⟨⟨y, hyH⟩, Subgroup.mem_centralizer_singleton_iff.mpr ?_, rfl⟩
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hyv)
  have hUeq : U = ((CFSG.pPrimeCore 2 A).map A.subtype).map H.subtype := by
    rw [← StationaryConfinement.ambient_core_of_subgroup_map H A]
    exact pPrimeCore_map_congr hXA.symm
  let e₁ : CFSG.pPrimeCore 2 A ≃* U :=
    (((CFSG.pPrimeCore 2 A).equivMapOfInjective _ A.subtype_injective).trans
      (((CFSG.pPrimeCore 2 A).map A.subtype).equivMapOfInjective _
        H.subtype_injective)).trans (MulEquiv.subgroupCongr hUeq.symm)
  let e₂ : CFSG.pPrimeCore 2 A ≃*
      CFSG.pPrimeCore 2 (Subgroup.centralizer ({θ v'} : Set (PGL2 F'))) :=
    ((CFSG.pPrimeCore 2 A).equivMapOfInjective _ ψ.injective).trans
      (MulEquiv.subgroupCongr hcore)
  have hUcard : Nat.card U = m := by
    rw [← Nat.card_congr e₁.toEquiv, Nat.card_congr e₂.toEquiv, hOcard']
  have hUcyc : IsCyclic U :=
    isCyclic_of_surjective (e₂.symm.trans e₁).toMonoidHom (e₂.symm.trans e₁).surjective
  have hUK : U ≤ K := by
    rintro _ ⟨y, hy, rfl⟩
    have hyH : (y : G) ∈ H := (Subgroup.mem_inf.mp y.2).1
    have hodd : Odd (orderOf (y : G)) := by
      rw [Subgroup.orderOf_coe]
      exact (Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := X))).of_dvd_nat
        (Subgroup.orderOf_dvd_natCard _ hy)
    have hmem := mem_of_index_two_of_odd (Y := K.subgroupOf H) hKH2
      (x := ⟨(y : G), hyH⟩) (by rw [Subgroup.orderOf_mk]; exact hodd)
    exact Subgroup.mem_subgroupOf.mp hmem
  have htA : t' ∈ A := by
    refine Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext ?_)
    show t * (s * d) = s * d * t
    calc t * (s * d) = (t * s) * d := by group
      _ = (s * t) * d := by rw [hL.ts]
      _ = s * (t * d) := by group
      _ = s * (d * t) := by rw [hL.t_comm_J d hL.d_mem]
      _ = s * d * t := by group
  have hvA : v' ∈ A := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hψt : ((ψ ⟨t', htA⟩ : Subgroup.centralizer ({θ v'} : Set (PGL2 F'))) : PGL2 F') ∉ U₁ := by
    intro hU
    have h1 : ((ψ ⟨t', htA⟩ : Subgroup.centralizer ({θ v'} : Set (PGL2 F'))) : PGL2 F') = θ v' := by
      apply huniq _ hU _ hxU₁ _ hx2 _ hx1
      · rw [hψ, ← map_mul]
        show θ (t' * t') = 1
        rw [ht'2, map_one]
      · rw [hψ]
        intro h2
        have h3 := (hθ t').mp h2
        exact hL.not_odd_t (hL.W_odd t (hOW t' h3))
    rw [hψ] at h1
    have h2 : t' = v' := Subtype.ext (congrArg Subtype.val (hinj htA hvA h1))
    have h3 : t = s * d := congrArg Subtype.val h2
    apply hL.s_not_mem_J
    have h4 : s = t * d⁻¹ := by rw [h3]; group
    rw [h4]
    exact J.mul_mem hL.t_mem (J.inv_mem hL.d_mem)
  have htinv : ∀ u ∈ U, t * u * t⁻¹ = u⁻¹ := by
    intro u hu
    rw [hUeq] at hu
    obtain ⟨_, ⟨o, ho, rfl⟩, rfl⟩ := hu
    have hψo : ψ o ∈ CFSG.pPrimeCore 2 (Subgroup.centralizer ({θ v'} : Set (PGL2 F'))) := by
      rw [← hcore]
      exact ⟨o, ho, rfl⟩
    have h1 := hOinv (ψ ⟨t', htA⟩) hψt (ψ o) hψo
    rw [← map_inv, ← map_mul, ← map_mul, ← map_inv] at h1
    have h2 := ψ.injective h1
    have h3 := congrArg (fun a : A => ((a : H) : G)) h2
    simpa using h3
  have hcop : Nat.Coprime (Nat.card U) (Nat.card B) := by
    rw [hUcard]
    have h2m : (2 * (m : ℤ)) = q' + e' := by
      rw [← hU₁card', hm2]
      push_cast
      ring
    set c := Nat.gcd m (Nat.card B) with hc
    have hcm : c ∣ m := Nat.gcd_dvd_left _ _
    have hcB : c ∣ Nat.card B := Nat.gcd_dvd_right _ _
    have hc2 : (c : ℤ) ∣ 2 * e' := by
      have h1 : (c : ℤ) ∣ 2 * m := dvd_mul_of_dvd_right (by exact_mod_cast hcm) 2
      have h2 : (c : ℤ) ∣ 4 * Nat.card B := dvd_mul_of_dvd_right (by exact_mod_cast hcB) 4
      have h3 := dvd_sub h1 h2
      rw [h2m, h4B] at h3
      have h4 : (q' : ℤ) + e' - (q' - e') = 2 * e' := by ring
      rwa [h4] at h3
    have he1 : e' = 1 ∨ e' = -1 := by
      show (if q' % 4 = 1 then (1 : ℤ) else -1) = 1 ∨ (if q' % 4 = 1 then (1 : ℤ) else -1) = -1
      split_ifs <;> simp
    have hc2' : c ∣ 2 := by
      rcases he1 with h | h <;> rw [h] at hc2 <;> [skip; rw [mul_neg, dvd_neg] at hc2] <;>
        exact_mod_cast hc2
    have hcodd : Odd c := hmodd.of_dvd_nat hcm
    rcases (Nat.dvd_prime Nat.prime_two).mp hc2' with h | h
    · exact h
    · rw [h] at hcodd
      exact absurd hcodd (by decide)
  have h2U : 2 * (Nat.card U : ℤ) = q' + e' := by
    rw [hUcard, ← hU₁card', hm2]
    push_cast
    ring
  exact ⟨hq'3, h4B, hvo, hvH, hvK, hUcyc, h2U, hUK, htinv, hcop⟩

end CFSG.Semidihedral.FixedCoreNontrivial
