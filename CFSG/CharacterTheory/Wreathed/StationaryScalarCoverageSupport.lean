module

public import CFSG.CharacterTheory.Wreathed.CyclingAbelianQuotientOddControl
public import CFSG.CharacterTheory.Wreathed.LocalizedFixedPoints

public section

namespace CFSG.Wreathed.StationaryScalarCoverage

open scoped Pointwise
open CFSG.SignalizerFunctor.Helpers
open CFSG.Semidihedral.StationaryOddLocalization
open CFSG.Wreathed.LocalizedFixedPoints

universe u

variable {G : Type u} [Group G]

theorem map_conj_map_subtype (K : Subgroup G) (P : Subgroup K) (c : K) :
    (P.map (MulAut.conj c).toMonoidHom).map K.subtype =
      (P.map K.subtype).map (MulAut.conj (c : G)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem map_subtype_smul_sylow {ell : ℕ} (K : Subgroup G) (P : Sylow ell K) (c : K) :
    ((c • P : Sylow ell K) : Subgroup K).map K.subtype =
      ((P : Subgroup K).map K.subtype).map (MulAut.conj (c : G)).toMonoidHom := by
  rw [Sylow.coe_subgroup_smul]
  exact map_conj_map_subtype K (P : Subgroup K) c

theorem exists_mul_mem_normalizer_sylow [Finite G] {ell : ℕ} [Fact ell.Prime]
    {D : Subgroup G} (P : Sylow ell D) {g : G} (hg : g ∈ Subgroup.normalizer (D : Set G)) :
    ∃ d ∈ D, d * g ∈
      Subgroup.normalizer (((P : Subgroup D).map D.subtype : Subgroup G) : Set G) := by
  let ψ : D →* D := (D.normalizerMonoidHom ⟨g, hg⟩).toMonoidHom
  have hψ : Function.Surjective ψ := (D.normalizerMonoidHom ⟨g, hg⟩).surjective
  obtain ⟨d, hd⟩ := MulAction.exists_smul_eq D (P.mapSurjective hψ) P
  refine ⟨d, d.2, ?_⟩
  have h1 := map_subtype_smul_sylow D (P.mapSurjective hψ) d
  have hcomp : D.subtype.comp ψ = (MulAut.conj g).toMonoidHom.comp D.subtype := by
    ext k
    rfl
  have h2 : ((P : Subgroup D).map ψ).map D.subtype =
      ((P : Subgroup D).map D.subtype).map (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.map_map, Subgroup.map_map, hcomp]
  rw [hd, Sylow.coe_mapSurjective, h2, Subgroup.map_map] at h1
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine Eq.trans ?_ h1.symm
  congr 1
  ext k
  simp [mul_assoc]

theorem exists_invariant_sylow_containing [Finite G] {ell : ℕ} (hell : ell.Prime)
    (V K W : Subgroup G) (hV2 : IsPGroup 2 V) (hKodd : Odd (Nat.card K))
    (hVK : V ≤ Subgroup.normalizer (K : Set G)) (hWK : W ≤ K) (hWp : IsPGroup ell W)
    (hVW : V ≤ Subgroup.normalizer (W : Set G)) :
    ∃ Q : Sylow ell K, W ≤ (Q : Subgroup K).map K.subtype ∧
      V ≤ Subgroup.normalizer (((Q : Subgroup K).map K.subtype : Subgroup G) : Set G) := by
  let _action := conjugationAction V K hVK
  obtain ⟨Q, hWQ, hQInv⟩ := invariant_sylow_containing 2 ell Nat.prime_two hell
    hV2 hKodd.coprime_two_left (W.subgroupOf K) (hWp.comap_subtype)
    (normalized_subgroup_invariant_subgroup V K W hVK hVW)
  refine ⟨Q, ?_, ?_⟩
  · have h := Subgroup.map_mono (f := K.subtype) hWQ
    rwa [Subgroup.map_subgroupOf_eq_of_le hWK] at h
  · apply invariant_subgroup_map_normalized V K hVK (Q : Subgroup K)
    change ∀ a : V, ∀ z ∈ (Q : Subgroup K), a • z ∈ (Q : Subgroup K)
    intro a z hz
    have himage := Subgroup.smul_mem_pointwise_smul z a (Q : Subgroup K) hz
    rw [← Sylow.pointwise_smul_def, hQInv] at himage
    exact himage

theorem exists_mem_normalizer_not_mem [Finite G] {ell : ℕ} [Fact ell.Prime] {Q U : Subgroup G}
    (hQ : IsPGroup ell Q) (hUQ : U ≤ Q) (hQU : ¬ Q ≤ U) :
    ∃ z ∈ Q, z ∈ Subgroup.normalizer (U : Set G) ∧ z ∉ U := by
  have hlt : U.subgroupOf Q < ⊤ :=
    lt_top_iff_ne_top.mpr fun h => hQU (Subgroup.subgroupOf_eq_top.mp h)
  have h := CFSG.LocalAnalysis.ComponentInitial.p_group_normalizer_condition hQ hlt
  obtain ⟨z, hzN, hzU⟩ := IsConcreteLE.exists_of_lt h
  have hcomap : (Subgroup.normalizer (U : Set G)).comap Q.subtype =
      Subgroup.normalizer (U.subgroupOf Q : Set Q) :=
    Subgroup.comap_normalizer_eq_of_le_range (hUQ.trans_eq Q.range_subtype.symm)
  rw [← hcomap] at hzN
  exact ⟨z, z.2, hzN, hzU⟩

theorem le_normalizer_map_pPrimeCore (H : Subgroup G) :
    H ≤ Subgroup.normalizer (((CFSG.pPrimeCore 2 H).map H.subtype : Subgroup G) : Set G) :=
  characteristic_subgroup_map_normalized H H H.le_normalizer (CFSG.pPrimeCore 2 H)

theorem inf_map_pPrimeCore_le [Finite G] {A K : Subgroup G} (hAK : A ≤ K) :
    A ⊓ (CFSG.pPrimeCore 2 K).map K.subtype ≤ (CFSG.pPrimeCore 2 A).map A.subtype := by
  let X := A ⊓ (CFSG.pPrimeCore 2 K).map K.subtype
  have hXA : X ≤ A := inf_le_left
  have hn : (X.subgroupOf A).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      ((le_inf Subgroup.le_normalizer (hAK.trans (le_normalizer_map_pPrimeCore K))).trans
        Subgroup.inf_normalizer_le_normalizer_inf)
  have hodd : Nat.Coprime 2 (Nat.card (X.subgroupOf A)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXA).toEquiv]
    have hR : Nat.Coprime 2 (Nat.card ((CFSG.pPrimeCore 2 K).map K.subtype)) := by
      rw [Subgroup.card_map_of_injective K.subtype_injective]
      exact CFSG.pPrimeCore_coprime_card
    exact hR.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right)
  have hle : X.subgroupOf A ≤ CFSG.pPrimeCore 2 A := le_sSup ⟨hn, hodd⟩
  have hmap := Subgroup.map_mono (f := A.subtype) hle
  rwa [Subgroup.map_subgroupOf_eq_of_le hXA] at hmap

theorem mk_mem_center_of_commutator_mem {A : Subgroup G} {t : G} (htA : t ∈ A)
    (h : ∀ a ∈ A, a * t * a⁻¹ * t⁻¹ ∈ (CFSG.pPrimeCore 2 A).map A.subtype) :
    (QuotientGroup.mk (⟨t, htA⟩ : A) : A ⧸ CFSG.pPrimeCore 2 A) ∈
      Subgroup.center (A ⧸ CFSG.pPrimeCore 2 A) := by
  rw [Subgroup.mem_center_iff]
  intro q
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
  have hmem : a * ⟨t, htA⟩ * a⁻¹ * (⟨t, htA⟩ : A)⁻¹ ∈ CFSG.pPrimeCore 2 A := by
    obtain ⟨r, hr, hreq⟩ := h a a.2
    have heq : a * ⟨t, htA⟩ * a⁻¹ * (⟨t, htA⟩ : A)⁻¹ = r := Subtype.ext hreq.symm
    rw [heq]
    exact hr
  have h1 : (QuotientGroup.mk (a * ⟨t, htA⟩ * a⁻¹ * (⟨t, htA⟩ : A)⁻¹) :
      A ⧸ CFSG.pPrimeCore 2 A) = 1 := (QuotientGroup.eq_one_iff _).mpr hmem
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
    QuotientGroup.mk_inv, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
  exact h1

theorem commutator_mem_of_mul_eq {K O : Subgroup G} {x a : G} (hxK : x ∈ K)
    (hKO : K ≤ Subgroup.normalizer (O : Set G))
    (hfac : (O : Set G) * ((K ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) : Set G) =
      (K : Set G)) (ha : a ∈ K) : a * x * a⁻¹ * x⁻¹ ∈ O := by
  have ha' : a ∈ (O : Set G) *
      ((K ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) : Set G) := by
    rw [hfac]
    exact ha
  obtain ⟨o, ho, c, hc, rfl⟩ := ha'
  have hcx : c * x = x * c := Subgroup.mem_centralizer_singleton_iff.mp hc.2
  have hxo : x * o⁻¹ * x⁻¹ ∈ O :=
    (Subgroup.mem_normalizer_iff.mp (hKO hxK) o⁻¹).mp (O.inv_mem ho)
  have heq : o * c * x * (o * c)⁻¹ * x⁻¹ = o * (x * o⁻¹ * x⁻¹) := by
    calc o * c * x * (o * c)⁻¹ * x⁻¹ = o * (c * x) * c⁻¹ * o⁻¹ * x⁻¹ := by group
      _ = o * (x * c) * c⁻¹ * o⁻¹ * x⁻¹ := by rw [hcx]
      _ = o * (x * o⁻¹ * x⁻¹) := by group
  rw [heq]
  exact O.mul_mem ho hxo

theorem mem_centralizer_of_pair (T : Subgroup G) [IsKleinFour T] {x y g : G} (hxT : x ∈ T)
    (hyT : y ∈ T) (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hxy : x ≠ y)
    (hgx : g ∈ Subgroup.centralizer ({x} : Set G))
    (hgy : g ∈ Subgroup.centralizer ({y} : Set G)) :
    g ∈ Subgroup.centralizer (T : Set G) := by
  have hx : Commute g x := Subgroup.mem_centralizer_singleton_iff.mp hgx
  have hy : Commute g y := Subgroup.mem_centralizer_singleton_iff.mp hgy
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  rcases CFSG.Semidihedral.Local.kleinFour_mem_cases T hxT hyT hx1 hy1 hxy hv with
    rfl | rfl | rfl | rfl
  · exact (hx.mul_right hy).eq.symm
  · exact hx.eq.symm
  · exact hy.eq.symm
  · rw [one_mul, mul_one]

theorem stationary_of_map_conj [Finite G] {ell : ℕ} (hell : ell.Prime) (P P' : Subgroup G)
    (g : G) (hP' : P.map (MulAut.conj g).toMonoidHom = P')
    (hstationary : ∃ Q : Sylow ell (CFSG.pPrimeCore 2 (Subgroup.normalizer (P : Set G))),
      ((Q : Subgroup _).map (CFSG.pPrimeCore 2
        (Subgroup.normalizer (P : Set G))).subtype).map
          (Subgroup.normalizer (P : Set G)).subtype = P) :
    ∃ Q : Sylow ell (CFSG.pPrimeCore 2 (Subgroup.normalizer (P' : Set G))),
      ((Q : Subgroup _).map (CFSG.pPrimeCore 2
        (Subgroup.normalizer (P' : Set G))).subtype).map
          (Subgroup.normalizer (P' : Set G)).subtype = P' := by
  subst hP'
  exact stationary_sylow_to_intrinsic_core hell _
    (stationary_sylow_map_isomorphism hell (MulAut.conj g) P
      (stationary_sylow_from_intrinsic_core hell P hstationary))

theorem false_of_intermediate_fixed_subgroup [Finite G] {ell : ℕ} (hell : ell.Prime)
    (hellodd : Odd ell) (T : Subgroup G) [IsKleinFour T] {x y : G} (hxT : x ∈ T)
    (hyT : y ∈ T) (hx2 : orderOf x = 2) (hy2 : orderOf y = 2) (hxy : x ≠ y) (a b : ℕ)
    (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hCD : Nonempty (Subgroup.centralizer (T : Set G) ⧸
        CFSG.pPrimeCore 2 (Subgroup.centralizer (T : Set G)) ≃*
      Multiplicative (ZMod (2 ^ a)) × Multiplicative (ZMod (2 ^ b))))
    {D : Subgroup G} (hDC : D ≤ Subgroup.centralizer (T : Set G))
    (hoddD : ∀ c ∈ Subgroup.centralizer (T : Set G), Odd (orderOf c) → c ∈ D)
    (PD : Sylow ell D) {Q F : Subgroup G} (hQp : IsPGroup ell Q)
    (hPDQ : (PD : Subgroup D).map D.subtype ≤ Q) (hTQ : T ≤ Subgroup.normalizer (Q : Set G))
    (hQx : Q ≤ Subgroup.centralizer ({x} : Set G))
    (hQD : Q ⊓ D ≤ (PD : Subgroup D).map D.subtype)
    (hQPD : ¬ Q ≤ (PD : Subgroup D).map D.subtype)
    (hFPD : F ≤ (PD : Subgroup D).map D.subtype)
    (hFx : F ≤ Subgroup.centralizer ({x} : Set G)) {g : G}
    (hgH : g ∈ Subgroup.normalizer (((PD : Subgroup D).map D.subtype : Subgroup G) : Set G))
    (hgT : g ∈ Subgroup.normalizer (T : Set G)) (hg : ∀ v ∈ T, v ≠ 1 → g * v * g⁻¹ ≠ v)
    (hgy : g * y * g⁻¹ = x)
    (hfac : (((CFSG.pPrimeCore 2 (Subgroup.normalizer (F : Set G))).map
        (Subgroup.normalizer (F : Set G)).subtype : Subgroup G) : Set G) *
      ((Subgroup.normalizer (F : Set G) ⊓ Subgroup.centralizer ({x} : Set G) :
        Subgroup G) : Set G) = (Subgroup.normalizer (F : Set G) : Set G))
    (hloc : ∀ W : Subgroup G, W ≤ Subgroup.normalizer (F : Set G) → IsPGroup ell W →
      x ∈ Subgroup.normalizer (W : Set G) → W ≤ Subgroup.centralizer ({x} : Set G)) :
    False := by
  have : Fact ell.Prime := ⟨hell⟩
  set PDa := (PD : Subgroup D).map D.subtype with hPDa
  set H := Subgroup.normalizer (PDa : Set G) with hH
  set A := Subgroup.centralizer (PDa : Set G) with hA
  set K := Subgroup.normalizer (F : Set G) with hK
  set R := (CFSG.pPrimeCore 2 H).map H.subtype with hR
  have hx1 : x ≠ 1 := fun h => by
    rw [h, orderOf_one] at hx2
    omega
  have hy1 : y ≠ 1 := fun h => by
    rw [h, orderOf_one] at hy2
    omega
  have hT2 : IsPGroup 2 T :=
    IsPGroup.of_card (n := 2) (by rw [IsKleinFour.card_four]; norm_num)
  obtain ⟨x₀, hx₀Q, hx₀H, hx₀PD⟩ := exists_mem_normalizer_not_mem hQp hPDQ hQPD
  have hPDaD : PDa ≤ D := Subgroup.map_subtype_le _
  have hAH : A ≤ H := Subgroup.centralizer_le_normalizer _
  have hTA : T ≤ A :=
    (Subgroup.le_centralizer_iff.mp hDC).trans (Subgroup.centralizer_le hPDaD)
  have hTH : T ≤ H := hTA.trans hAH
  have hAK : A ≤ K :=
    (Subgroup.centralizer_le hFPD).trans (Subgroup.centralizer_le_normalizer _)
  have hxK : x ∈ K := hAK (hTA hxT)
  have hcommA : ∀ c ∈ A, c * x * c⁻¹ * x⁻¹ ∈ (CFSG.pPrimeCore 2 A).map A.subtype := by
    intro c hc
    have hO : c * x * c⁻¹ * x⁻¹ ∈ (CFSG.pPrimeCore 2 K).map K.subtype :=
      commutator_mem_of_mul_eq hxK (le_normalizer_map_pPrimeCore K) hfac (hAK hc)
    have hxA := hTA hxT
    have hcA : c * x * c⁻¹ * x⁻¹ ∈ A :=
      A.mul_mem (A.mul_mem (A.mul_mem hc hxA) (A.inv_mem hc)) (A.inv_mem hxA)
    exact inf_map_pPrimeCore_le hAK ⟨hcA, hO⟩
  have hxc := mk_mem_center_of_commutator_mem (hTA hxT) hcommA
  obtain ⟨-, -, -, -, -, -, hcyc⟩ :=
    four_group_cycling_with_abelian_centralizer_quotient_controls_odd_subgroups
      T x y hxT hyT hx2 hy2 hxy a b ha hb hCD H A hTH hAH
      (Subgroup.normal_subgroupOf_centralizer_normalizer _) hTA hxc g hgH hgT hg
  set P₁ := Q ⊓ H with hP₁
  have hP₁p : IsPGroup ell P₁ := hQp.to_le inf_le_left
  have hP₁odd : Odd (Nat.card P₁) := odd_card_of_pgroup hell hellodd P₁ hP₁p
  have hTP₁ : T ≤ Subgroup.normalizer (P₁ : Set G) :=
    (le_inf hTQ (hTH.trans Subgroup.le_normalizer)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hP₁R : P₁ ≤ R := hcyc P₁ inf_le_right hP₁odd hTP₁
  have hHR : H ≤ Subgroup.normalizer (R : Set G) := le_normalizer_map_pPrimeCore H
  have hRodd : Odd (Nat.card R) := by
    rw [Subgroup.card_map_of_injective H.subtype_injective]
    exact Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card
  obtain ⟨Ws, hP₁W, hTW⟩ := exists_invariant_sylow_containing hell T R P₁ hT2 hRodd
    (hTH.trans hHR) hP₁R hP₁p hTP₁
  set W := (Ws : Subgroup R).map R.subtype with hW
  have hWp : IsPGroup ell W := Ws.isPGroup'.map R.subtype
  have hWR : W ≤ R := Subgroup.map_subtype_le _
  have hx₀W : x₀ ∈ W := hP₁W ⟨hx₀Q, hx₀H⟩
  have hyW : ¬ W ≤ Subgroup.centralizer ({y} : Set G) := by
    intro hWy
    have hx₀C := mem_centralizer_of_pair T hxT hyT hx1 hy1 hxy (hQx hx₀Q) (hWy hx₀W)
    have hx₀odd : Odd (orderOf x₀) :=
      (odd_card_of_pgroup hell hellodd Q hQp).of_dvd_nat (Subgroup.orderOf_dvd_natCard Q hx₀Q)
    exact hx₀PD (hQD ⟨hx₀Q, hoddD x₀ hx₀C hx₀odd⟩)
  have hxW : ¬ W ≤ Subgroup.centralizer ({x} : Set G) := by
    intro hWx
    have hxR : x ∈ Subgroup.normalizer (R : Set G) := hHR (hTH hxT)
    have hgR : g ∈ Subgroup.normalizer (R : Set G) := hHR hgH
    let Wg := W.map (MulAut.conj g).toMonoidHom
    have hWgR : Wg ≤ R := by
      rintro _ ⟨w, hw, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp hgR w).mp (hWR hw)
    have hxWg : x ∈ Subgroup.normalizer (Wg : Set G) := by
      have h1 := Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom (hTW hyT)
      rw [Subgroup.map_equiv_normalizer_eq] at h1
      change g * y * g⁻¹ ∈ _ at h1
      rwa [hgy] at h1
    have hWgC := centralized_invariant_pgroups_of_centralized_sylow hell x hx2 R hRodd hxR Ws
      (hTW hxT) hWx Wg hWgR (hWp.map _) hxWg
    apply hyW
    intro w hw
    have h1 : g * w * g⁻¹ * x = x * (g * w * g⁻¹) :=
      Subgroup.mem_centralizer_singleton_iff.mp
        (hWgC (Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hw))
    rw [Subgroup.mem_centralizer_singleton_iff]
    rw [← hgy] at h1
    have h2 : g * (w * y) * g⁻¹ = g * (y * w) * g⁻¹ := by
      calc g * (w * y) * g⁻¹ = g * w * g⁻¹ * (g * y * g⁻¹) := by group
        _ = g * y * g⁻¹ * (g * w * g⁻¹) := h1
        _ = g * (y * w) * g⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h2)
  obtain ⟨v, hvW, -, hvinv, hvcomm, hvC⟩ :=
    odd_pgroup_inverted_centralizing_witness hell hellodd x hx2 W hWp (hTW hxT) hxW
  have hFW : F ≤ W := fun f hf => hP₁W ⟨hPDQ (hFPD hf), Subgroup.le_normalizer (hFPD hf)⟩
  have hvK : v ∈ K := by
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    exact (hvcomm f ⟨hFW hf, hFx hf⟩).eq.symm
  have hlocv := hloc (Subgroup.zpowers v) (Subgroup.zpowers_le.mpr hvK)
    (hWp.to_le (Subgroup.zpowers_le.mpr hvW)) (mem_normalizer_zpowers_of_inv hvinv)
  exact hvC (hlocv (Subgroup.mem_zpowers v))

end CFSG.Wreathed.StationaryScalarCoverage
