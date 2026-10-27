module

public import CFSG.HardMathSupport.Solomon.Coordinator.I25_3Fix
public import CFSG.HardMathSupport.Solomon.Coordinator.I25_3K
public import CFSG.HardMathSupport.Solomon.Coordinator.I25_3Elem
public import CFSG.HardMathSupport.Solomon.Coordinator.B3Red
public import CFSG.HardMathSupport.Solomon.Coordinator.B3Local
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514Cover

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns
open scoped commutatorElement

theorem i253_layer (h181 : LocalBalance.Lemma514CoverNs.Input18_1) {Y : Type} [Group Y] [Finite Y]
    {K J : Subgroup Y} {b a : Y} (hKK : CFSG.Open.IsKGroup ↥K) (hbK : b ∈ K) (hb3 : orderOf b = 3)
    (hJ : CFSG.Open.IsComponentOf J (K ⊓ Subgroup.centralizer ({b} : Set Y))) (hbJ : b ∈ J)
    (hZ : Subgroup.center (barOf 3 J) = Subgroup.zpowers (QuotientGroup.mk (⟨b, hbJ⟩ : ↥J)))
    {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) (hpc : SL3EpsOfChar p (barOf 3 J))
    (haK : a ∈ Subgroup.normalizer (K : Set Y)) (haJ : a ∈ Subgroup.normalizer (J : Set Y))
    (ha3 : a ^ 3 = 1) (hab : a * b = b * a)
    (hfa : IsFieldAutThree (barAut 3 J ⟨a, haJ⟩))
    (h8 : barAut 3 J ⟨a, haJ⟩ ≠ 1 → ¬ IsSU38 (barOf 3 J)) :
    (⟨b, hbK⟩ : ↥K) ∈ GLAPLayer 3 (fixSubgroup (i253α K a haK)) ∧
      ∃ u : ↥J, IsPGroup p ↥(Subgroup.zpowers (u : Y)) ∧ (u : Y) * a = a * u ∧
        (u : Y) * b = b * u ∧ QuotientGroup.mk' (GLAPPrimeCore 3 ↥J) u ≠ 1 := by
  have hJq : CFSG.Open.IsQuasisimple ↥J := hJ.2.2
  have hJK : J ≤ K := hJ.1.trans inf_le_left
  have hb3' : b ^ 3 = 1 := by have := pow_orderOf_eq_one b; rwa [hb3] at this
  have hb1 : b ≠ 1 := fun h => by rw [h, orderOf_one] at hb3; omega
  set b' : ↥J := ⟨b, hbJ⟩ with hb'
  have hb'3 : b' ^ 3 = 1 := Subtype.ext (by simpa using hb3')
  have hb'1 : b' ≠ 1 := fun h => hb1 (congrArg Subtype.val h)
  have hb'o : orderOf b' = 3 := by
    rw [orderOf_eq_prime_iff]; exact ⟨hb'3, hb'1⟩
  have h3J : 3 ∣ Nat.card ↥J := by rw [← hb'o]; exact orderOf_dvd_natCard b'
  have hOc := i253_primeCore_le_center hJq h3J
  set π := QuotientGroup.mk' (GLAPPrimeCore 3 ↥J) with hπ
  have hker : π.ker ≤ Subgroup.center ↥J := by rw [hπ, QuotientGroup.ker_mk']; exact hOc
  have hQbar : CFSG.Open.IsQuasisimple (barOf 3 J) :=
    i253_isQuasisimple_of_surj hJq π (QuotientGroup.mk'_surjective _) hker
  have hbZ : π b' ∈ Subgroup.center (barOf 3 J) := by
    rw [hZ]; exact Subgroup.mem_zpowers _
  have hπb1 : π b' ≠ 1 := by
    intro h
    have hO : b' ∈ GLAPPrimeCore 3 ↥J := (QuotientGroup.eq_one_iff _).1 h
    have h1 : orderOf b' ∣ Nat.card (GLAPPrimeCore 3 ↥J) :=
      Subgroup.orderOf_dvd_natCard _ hO
    have hcop := coprime_card_gLAPPrimeCore_aux 3 ↥J
    rw [hb'o] at h1
    exact absurd (Nat.eq_one_of_dvd_coprimes hcop (dvd_refl 3) h1) (by norm_num)
  set αJ : MulAut ↥J := J.normalizerMonoidHom ⟨a, haJ⟩ with hαJ
  set β : MulAut (barOf 3 J) := barAut 3 J ⟨a, haJ⟩ with hβ
  have hβ3 : β ^ 3 = 1 := by
    have h : (⟨a, haJ⟩ : ↥(Subgroup.normalizer (J : Set Y))) ^ 3 = 1 :=
      Subtype.ext (by simpa using ha3)
    rw [hβ, ← map_pow, h, map_one]
  have hαβ : ∀ x, π (αJ x) = β (π x) := fun x => (barAut_mk 3 J ⟨a, haJ⟩ x).symm
  obtain ⟨hSq, hSZ, h3S, hSz3, hSx⟩ := i253_fixStruct hQbar hp hpc ⟨π b', hbZ, hπb1⟩ hβ3 hfa h8
  have hSO : GLAPPrimeCore 3 ↥(fixSubgroup β) = ⊥ := i253_primeCore_bot hSq h3S hSz3
  obtain ⟨T, hT, hbT, hbc, ⟨u, huT, hup, huπ⟩, hTq, h3T⟩ :=
    i253_ja hJq hp hp3 αJ β hαβ hSq hSO hSZ h3S hSx b' hb'3 hb'1 hbZ
  have hTα : T ≤ fixSubgroup αJ := hT.1
  obtain ⟨k, hk⟩ := hup ⟨u, Subgroup.mem_zpowers u⟩
  have huk : (u : Y) ^ (p ^ k) = 1 := by
    have h1 : u ^ (p ^ k) = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have := congrArg Subtype.val h1
    simpa using this
  refine ⟨?_, ⟨u, i253_isPGroup_zpowers huk, ?_, ?_, huπ⟩⟩
  · set ι : ↥J →* ↥K := Subgroup.inclusion hJK with hι
    have hιinj : Function.Injective ι := Subgroup.inclusion_injective hJK
    set bK : ↥K := ⟨b, hbK⟩ with hbKdef
    have hbN : b ∈ Subgroup.normalizer (K : Set Y) := Subgroup.le_normalizer hbK
    set fa := fixSubgroup (i253α K a haK) with hfa_def
    set fb := fixSubgroup (i253α K b hbN) with hfb_def
    have hCD : fb = Subgroup.centralizer ((Subgroup.zpowers bK : Subgroup ↥K) : Set ↥K) := by
      ext x
      rw [mem_fixSubgroup_i253α, mem_centralizer_zpowers_iff]
      constructor
      · intro h; exact Subtype.ext h
      · intro h; exact congrArg Subtype.val h
    have hker1 : Nat.Coprime 3 (Nat.card ↥(fixSubgroup αJ ⊓ ι.ker)) := by
      rw [(MonoidHom.ker_eq_bot_iff ι).2 hιinj, inf_bot_eq, Subgroup.card_bot]
      exact Nat.coprime_one_right _
    have hTK := glaPComponent_map Nat.prime_three ι hker1 hT
    have hM : (fixSubgroup αJ).map ι = J.subgroupOf K ⊓ fa := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        refine ⟨x.2, (mem_fixSubgroup_i253α K a haK (ι x)).2 ?_⟩
        have h1 : αJ x = x := hx
        have h2 := congrArg Subtype.val h1
        have : ((αJ x : ↥J) : Y) = a * x * a⁻¹ :=
          Subgroup.normalizerMonoidHom_apply_apply_coe _ _ _
        rw [this] at h2
        show a * (x : Y) = (x : Y) * a
        calc a * (x : Y) = a * x * a⁻¹ * a := by group
          _ = x * a := by rw [h2]
      · rintro ⟨hyJ, hyf⟩
        refine ⟨⟨y, hyJ⟩, ?_, rfl⟩
        have h1 := (mem_fixSubgroup_i253α K a haK y).1 hyf
        show αJ ⟨y, hyJ⟩ = ⟨y, hyJ⟩
        apply Subtype.ext
        have : ((αJ ⟨y, hyJ⟩ : ↥J) : Y) = a * y * a⁻¹ :=
          Subgroup.normalizerMonoidHom_apply_apply_coe _ _ _
        rw [this, h1]; group
    have hJsn : IsSubnormal (J.subgroupOf K) fb := by
      have h1 := isSubnormal_comap' K.subtype hJ.2.1
      have h2 : (K ⊓ Subgroup.centralizer ({b} : Set Y)).comap K.subtype = fb := by
        ext x
        rw [hfb_def, mem_fixSubgroup_i253α]
        constructor
        · rintro ⟨-, hx⟩
          have := Subgroup.mem_centralizer_singleton_iff.1 hx
          exact this.symm
        · intro h
          refine ⟨x.2, Subgroup.mem_centralizer_singleton_iff.2 h.symm⟩
      rw [h2] at h1
      exact h1
    have hsn1 : IsSubnormal (J.subgroupOf K ⊓ fa) (fb ⊓ fa) := isSubnormal_inf hJsn fa
    have hX : fa ⊓ Subgroup.centralizer ((Subgroup.zpowers bK : Subgroup ↥K) : Set ↥K) = fb ⊓ fa := by
      rw [← hCD, inf_comm]
    have hsnT : IsSubnormal (T.map ι) (fb ⊓ fa) := by
      have := hTK.2.1
      rw [hM] at this
      exact isSubnormal_trans' this hsn1
    have hTle : T.map ι ≤ fb ⊓ fa := CFSG.LocalAnalysis.GLTheoremB.isSubnormal_le' hsnT
    have hKq' : CFSG.Open.IsQuasisimple ↥(T.map ι) := i253_isQuasisimple_map ι hιinj hTq
    have h3' : 3 ∣ Nat.card ↥(T.map ι) := by
      rw [Subgroup.card_map_of_injective hιinj]; exact h3T
    have hcomp : GLAPComponent 3 (fa ⊓ Subgroup.centralizer ((Subgroup.zpowers bK : Subgroup ↥K) : Set ↥K))
        (T.map ι) := by
      rw [hX]
      exact i253_glaPComponent_of_subnormal hTle hsnT hKq' h3'
    have hKK' : CFSG.IsKGroup ↥fa :=
      isKGroup_of_openIsKGroup (openIsKGroup_of_subgroup (isKGroup_of_openIsKGroup hKK) fa)
    have hbfa : bK ∈ fa := by
      rw [hfa_def, mem_fixSubgroup_i253α]; exact hab
    have hQle : Subgroup.zpowers bK ≤ fa := by rw [Subgroup.zpowers_le]; exact hbfa
    have hQp : IsPGroup 3 ↥(Subgroup.zpowers bK) :=
      i253_isPGroup_zpowers (k := 1) (Subtype.ext (by simpa using hb3'))
    have h18 := h181 ↥K fa hKK' (Subgroup.zpowers bK) hQle hQp
    have hle : T.map ι ≤ GLAPLayer 3 (fa ⊓ Subgroup.centralizer
        ((Subgroup.zpowers bK : Subgroup ↥K) : Set ↥K)) := le_sSup hcomp
    have hmem : bK ∈ T.map ι := ⟨b', hbT, rfl⟩
    exact h18 (hle hmem)
  · have h1 : αJ u = u := hTα huT
    have h2 := congrArg Subtype.val h1
    have : ((αJ u : ↥J) : Y) = a * u * a⁻¹ := Subgroup.normalizerMonoidHom_apply_apply_coe _ _ _
    rw [this] at h2
    calc (u : Y) * a = a * u * a⁻¹ * a := by rw [h2]
      _ = a * u := by group
  · have := hbc u huT
    exact congrArg Subtype.val this

end CFSG.HardMathSupport.Solomon.Coordinator
