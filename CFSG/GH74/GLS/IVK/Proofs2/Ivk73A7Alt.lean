module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4AltEmb
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvAltTerm
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit35AltLarge
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4P1Lift

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.IVK.GHInv
open Equiv Equiv.Perm
open CFSG.ComponentClassification.HarrisLit

theorem alt_a7_finish_of_card {n : ℕ} {N K Q : Subgroup (Perm (Fin n))} {F : Finset (Fin n)}
    (hNA : alternatingGroup (Fin n) ≤ N) (hKF : K = altOn F) (hF7 : F.card = 7)
    (hK1 : K ≠ ⊥) (hQN : Q ≤ N) (hQK : ∀ q ∈ Q, ∀ k ∈ K, q * k = k * q)
    (hQ2 : IsPGroup 2 Q) (hQ4 : 4 ≤ Nat.card Q)
    (hterm : Terminal N K) :
    IsElementaryAbelian 2 ↥Q ∧ Nat.card Q = 4 ∧ n = 11 ∧ N ≤ alternatingGroup (Fin n) := by
  classical
  have hF5 : 5 ≤ F.card := by omega
  have hfixQ : ∀ q ∈ Q, ∀ x ∈ F, q x = x := fun q hq x hx =>
    fixes_of_commute_altOn hF5 (fun k hk => hQK q hq k (hKF ▸ hk)) hx
  have hmovQ : ∀ q ∈ Q, q * q = 1 → q ≠ 1 → ∀ x, x ∉ F → q x ≠ x :=
    fun q hq h2 h1 => moves_outside hF5 hKF hK1 hterm (hQN hq) h2 h1 (hQK q hq)
  have hx₀ : ∃ x, x ∉ F := by
    by_contra h
    push Not at h
    have hFtop : F = Finset.univ := Finset.eq_univ_of_forall h
    have hQbot : Q = ⊥ := by
      rw [eq_bot_iff]
      intro q hq
      rw [Subgroup.mem_bot]
      ext x
      exact congrArg Fin.val (hfixQ q hq x (by rw [hFtop]; exact Finset.mem_univ x))
    have hQcard1 : Nat.card Q = 1 := by rw [hQbot, Subgroup.card_bot]
    omega
  obtain ⟨x₀, hx₀F⟩ := hx₀
  have hFc_le4 : Fᶜ.card ≤ 4 := by
    by_contra hle
    have h5 : 5 ≤ Fᶜ.card := by omega
    obtain ⟨S, hSFc, hScard⟩ := Finset.exists_subset_card_eq h5
    let eS : ↥S ≃ Fin 5 := Fintype.equivFinOfCardEq (by simpa using hScard)
    let d : Perm (Fin 5) := Equiv.swap 0 1 * Equiv.swap 2 3
    have hdA : d ∈ alternatingGroup (Fin 5) := by
      rw [mem_alternatingGroup, Perm.sign_mul, Perm.sign_swap (by decide),
        Perm.sign_swap (by decide)]
      norm_num
    let x : alternatingGroup (Fin 5) := ⟨d, hdA⟩
    have hd2 : d * d = 1 := by
      have := CFSG.LocalAnalysis.ComponentInitial.swap_mul_swap_sq_of_ne
        (o := (0 : Fin 5)) (l := (2 : Fin 5)) (a := (1 : Fin 5)) (b := (3 : Fin 5))
        (by decide) (by decide) (by decide) (by decide)
      simpa [pow_two, d] using this
    have hx2 : x * x = 1 := by
      apply Subtype.ext
      simpa [x] using hd2
    have hd1 : d ≠ 1 := by
      intro h
      have h0 : d 0 = (0 : Fin 5) := by rw [h]; rfl
      have h1 : d 0 = (1 : Fin 5) := by
        change (Equiv.swap (0 : Fin 5) 1 * Equiv.swap (2 : Fin 5) 3) 0 = 1
        rw [Perm.mul_apply,
          Equiv.swap_apply_of_ne_of_ne (by decide : (0 : Fin 5) ≠ 2)
            (by decide : (0 : Fin 5) ≠ 3),
          Equiv.swap_apply_left]
      exact (by decide : (1 : Fin 5) ≠ 0) (h1.symm.trans h0)
    have hx1 : x ≠ 1 := fun h => hd1 (congrArg Subtype.val h)
    let y : alternatingGroup ↥S := Equiv.altCongrHom eS.symm x
    let τa : alternatingGroup (Fin n) := alternatingGroup.ofSubtype S y
    let τ : Perm (Fin n) := τa
    have hy2 : y * y = 1 := by
      rw [show y = Equiv.altCongrHom eS.symm x from rfl, ← map_mul, hx2, map_one]
    have hτ2 : τ * τ = 1 := by
      have h : τa * τa = 1 := by
        rw [show τa = alternatingGroup.ofSubtype S y from rfl, ← map_mul, hy2, map_one]
      exact congrArg Subtype.val h
    have hy1 : y ≠ 1 := by
      intro h
      apply hx1
      apply (Equiv.altCongrHom eS.symm).injective
      simpa [y] using h
    have hτ1 : τ ≠ 1 := by
      have hτa1 : τa ≠ 1 := fun h =>
        hy1 (alternatingGroup.ofSubtype_injective (by simpa using h))
      exact fun h => hτa1 (Subtype.ext h)
    have hτA : τ ∈ alternatingGroup (Fin n) := τa.2
    have hτN : τ ∈ N := hNA hτA
    have hτfixF : ∀ x ∈ F, τ x = x := by
      intro x hxF
      have hxS : x ∉ S := fun hx => (Finset.mem_compl.mp (hSFc hx)) hxF
      change Perm.ofSubtype (y : Perm ↥S) x = x
      exact Perm.ofSubtype_apply_of_not_mem (y : Perm ↥S) hxS
    have hτK : ∀ k ∈ K, τ * k = k * τ := by
      intro k hk
      have hk' : k ∈ altOn F := hKF ▸ hk
      exact (commute_of_symOn_of_fixes (altOn_le_symOn F hk') hτfixF).symm
    have hxfix4 : (x : Perm (Fin 5)) 4 = 4 := by
      change (Equiv.swap (0 : Fin 5) 1 * Equiv.swap (2 : Fin 5) 3) 4 = 4
      rw [Perm.mul_apply,
        Equiv.swap_apply_of_ne_of_ne (by decide : (4 : Fin 5) ≠ 2)
          (by decide : (4 : Fin 5) ≠ 3),
        Equiv.swap_apply_of_ne_of_ne (by decide : (4 : Fin 5) ≠ 0)
          (by decide : (4 : Fin 5) ≠ 1)]
    have hyfix : (y : Perm ↥S) (eS.symm 4) = eS.symm 4 := by
      simp [y, hxfix4]
    have hτfix_s : τ ((eS.symm 4 : ↥S) : Fin n) = ((eS.symm 4 : ↥S) : Fin n) := by
      change Perm.ofSubtype (y : Perm ↥S) ((eS.symm 4 : ↥S) : Fin n) = _
      rw [Perm.ofSubtype_apply_of_mem (f := (y : Perm ↥S))
        (a := ((eS.symm 4 : ↥S) : Fin n)) (eS.symm 4).2]
      exact congrArg Subtype.val hyfix
    have hs_notF : ((eS.symm 4 : ↥S) : Fin n) ∉ F :=
      fun h => (Finset.mem_compl.mp (hSFc (eS.symm 4).2)) h
    exact (moves_outside hF5 hKF hK1 hterm hτN hτ2 hτ1 hτK
      ((eS.symm 4 : ↥S) : Fin n) hs_notF) hτfix_s
  have hQc : Nat.card Q ≤ Fᶜ.card := card_le_card_compl hQ2 hfixQ hmovQ hx₀F
  have hFc4 : Fᶜ.card = 4 := by omega
  have hn11 : n = 11 := by
    have hcard := Finset.card_add_card_compl F
    rw [hF7, hFc4] at hcard
    simpa using hcard.symm
  have hNalt : N ≤ alternatingGroup (Fin n) :=
    le_alternatingGroup_of_card hNA hF5 hKF hK1 hterm (by omega)
  have hQcard : Nat.card Q = 4 := by omega
  have hQalt : Q ≤ altOn (Fᶜ) := by
    intro q hq
    rw [mem_altOn]
    constructor
    · intro x hx
      exact hfixQ q hq x (by simpa using hx)
    · exact mem_alternatingGroup.mp (hNalt (hQN hq))
  let e : altOn (Fᶜ) ≃* alternatingGroup {x // x ∈ Fᶜ} := (altOnEquiv (Fᶜ)).symm
  let fQ : ↥Q →* alternatingGroup {x // x ∈ Fᶜ} :=
    e.toMonoidHom.comp (Subgroup.inclusion hQalt)
  have hfinj : Function.Injective fQ :=
    e.injective.comp (Subgroup.inclusion_injective hQalt)
  let V : Subgroup (alternatingGroup {x // x ∈ Fᶜ}) := (⊤ : Subgroup ↥Q).map fQ
  let φ : ↥Q ≃* ↥V :=
    (Subgroup.topEquiv (G := ↥Q)).symm.trans
      (Subgroup.equivMapOfInjective (⊤ : Subgroup ↥Q) fQ hfinj)
  have hVcard : Nat.card V = 4 := by
    calc Nat.card V = Nat.card ↥Q := (Nat.card_congr φ.toEquiv).symm
      _ = 4 := hQcard
  have hV2 : IsPGroup 2 V := by
    apply IsPGroup.of_card (n := 2)
    rw [hVcard]
    norm_num
  obtain ⟨S, hVS⟩ := hV2.exists_le_sylow
  have hα4 : Nat.card {x // x ∈ Fᶜ} = 4 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    exact hFc4
  have hSk : S = alternatingGroup.kleinFour {x // x ∈ Fᶜ} :=
    alternatingGroup.two_sylow_eq_kleinFour_of_card_eq_four hα4 S
  have hVklein : V ≤ alternatingGroup.kleinFour {x // x ∈ Fᶜ} := by
    simpa [hSk] using hVS
  have hVeq : V = alternatingGroup.kleinFour {x // x ∈ Fᶜ} := by
    apply Subgroup.eq_of_le_of_card_ge hVklein
    rw [hVcard, alternatingGroup.kleinFour_card_of_card_eq_four hα4]
  have hVK : IsKleinFour ↥V := by
    rw [hVeq]
    exact alternatingGroup.kleinFour_isKleinFour hα4
  haveI : IsKleinFour ↥V := hVK
  have hVEl : IsElementaryAbelian 2 ↥V := by
    refine { toIsMulCommutative := IsKleinFour.isMulCommutative, exponent_dvd_p := ?_ }
    rw [IsKleinFour.exponent_two]
  have hQel : IsElementaryAbelian 2 ↥Q :=
    CFSG.IsElementaryAbelian.of_mulEquiv φ.symm hVEl
  exact ⟨hQel, hQcard, hn11, hNalt⟩

theorem alt_a7_perm_of_card {n : ℕ} {N K Q : Subgroup (Perm (Fin n))}
    (hNA : alternatingGroup (Fin n) ≤ N)
    (hK7 : (↥K ⧸ pPrimeCore 2 ↥K) ≃* alternatingGroup (Fin 7))
    (hQN : Q ≤ N) (hQK : ∀ q ∈ Q, ∀ k ∈ K, q * k = k * q)
    (hQ2 : IsPGroup 2 Q) (hQ4 : 4 ≤ Nat.card Q)
    (hterm : Terminal N K) {x : Perm (Fin n)} (hxQ : x ∈ Q) (hx2 : x * x = 1)
    (hcomp : IsTwoComponentIn K
      (Subgroup.centralizer ({x} : Set (Perm (Fin n))) ⊓ alternatingGroup (Fin n))) :
    IsElementaryAbelian 2 ↥Q ∧ Nat.card Q = 4 ∧ n = 11 ∧ N ≤ alternatingGroup (Fin n) := by
  have hcard7 : Nat.card (↥K ⧸ pPrimeCore 2 ↥K) = 2520 := by
    rw [Nat.card_congr hK7.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    norm_num [Nat.factorial]
  have hdvd : Nat.card (↥K ⧸ pPrimeCore 2 ↥K) ∣ Nat.card ↥K :=
    Subgroup.card_quotient_dvd_card _
  have hK2520 : 2520 ≤ Nat.card ↥K := Nat.le_of_dvd Nat.card_pos (hcard7 ▸ hdvd)
  have hK1 : K ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hK2520
    omega
  obtain ⟨hKF, hF7, -⟩ := L35.seven_fixed_of_full_a7_quotient hx2 hcomp hK7
  have hKF' : K = altOn x.supportᶜ := by
    rw [hKF]
    ext g
    rw [mem_altOn, CFSG.ComponentClassification.GSThmB.Catalog82A10.mem_altOn,
      Equiv.Perm.mem_alternatingGroup]
    constructor
    · rintro ⟨hsign, hsupp⟩
      refine ⟨fun y hyF => ?_, hsign⟩
      by_contra hy
      exact hyF (hsupp (Equiv.Perm.mem_support.mpr hy))
    · rintro ⟨hfix, hsign⟩
      refine ⟨hsign, fun y hy => ?_⟩
      by_contra hyF
      exact (Equiv.Perm.mem_support.mp hy) (hfix y hyF)
  exact alt_a7_finish_of_card hNA hKF' hF7 hK1 hQN hQK hQ2 hQ4 hterm

theorem ivk73_a7_alt_of_b {n : ℕ} (N : Type) [Group N] [Finite N]
    (L K Q : Subgroup N) (hLnorm : L.Normal)
    (hcent : ∀ x : N, (∀ l ∈ L, x * l = l * x) → x = 1)
    (e : ↥L ≃* alternatingGroup (Fin n))
    (hKL : K ≤ L) (hKq : IsQuasisimple ↥K)
    (eK7 : (↥K ⧸ pPrimeCore 2 ↥K) ≃* alternatingGroup (Fin 7))
    (hQsyl : IsSylowOf 2 Q (centralizer (K : Set N)))
    (b : N) (hbQ : b ∈ Q) (hb2 : orderOf b = 2)
    (hQ4 : 4 ≤ Nat.card ↥Q)
    (hterm : ∀ y : N, orderOf y = 2 → y ∈ centralizer (K : Set N) →
      IsCompIn (centralizer ({y} : Set N)) K) :
    IsElementaryAbelian 2 ↥Q ∧ Nat.card ↥Q = 4 ∧ n = 11 ∧ L = ⊤ := by
  classical
  have hcard7 : Nat.card (↥K ⧸ pPrimeCore 2 ↥K) = 2520 := by
    rw [Nat.card_congr eK7.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    norm_num [Nat.factorial]
  have hdvd : Nat.card (↥K ⧸ pPrimeCore 2 ↥K) ∣ Nat.card ↥K :=
    Subgroup.card_quotient_dvd_card _
  have hK2520 : 2520 ≤ Nat.card ↥K := Nat.le_of_dvd Nat.card_pos (hcard7 ▸ hdvd)
  have hn7 : 7 ≤ n := by
    by_contra hn
    have hn6 : n ≤ 6 := by omega
    have hAle : Nat.card (alternatingGroup (Fin n)) ≤ Nat.factorial n := by
      calc Nat.card (alternatingGroup (Fin n)) ≤ Nat.card (Perm (Fin n)) :=
            Subgroup.card_le_card_group _
        _ = Nat.factorial n := by rw [Nat.card_perm, Nat.card_fin]
    have hLcard : Nat.card ↥L = Nat.card (alternatingGroup (Fin n)) := Nat.card_congr e.toEquiv
    have hLKcard : Nat.card ↥K ≤ Nat.card ↥L := Subgroup.card_le_of_le hKL
    have hfac : Nat.factorial n ≤ Nat.factorial 6 := Nat.factorial_le hn6
    have h720 : Nat.factorial 6 < 2520 := by norm_num [Nat.factorial]
    omega
  haveI : L.Normal := hLnorm
  obtain ⟨ι, hι, hιL⟩ := exists_perm_embedding hn7 hcent e
  have hNA : alternatingGroup (Fin n) ≤ ι.range := by
    intro g hg
    refine ⟨((e.symm ⟨g, hg⟩ : ↥L) : N), ?_⟩
    rw [hιL]
    simp
  have hK7' : (↥(K.map ι) ⧸ pPrimeCore 2 ↥(K.map ι)) ≃* alternatingGroup (Fin 7) := by
    let eKJ : ↥K ≃* ↥(K.map ι) := K.equivMapOfInjective ι hι
    exact (QuotientGroup.congr (pPrimeCore 2 ↥K) (pPrimeCore 2 ↥(K.map ι)) eKJ
      (pPrimeCore_map_iso 2 eKJ)).symm.trans eK7
  have hQN' : Q.map ι ≤ ι.range := Subgroup.map_le_range ι Q
  have hQK' : ∀ q ∈ Q.map ι, ∀ k ∈ K.map ι, q * k = k * q := by
    rintro _ ⟨q, hq, rfl⟩ _ ⟨k, hk, rfl⟩
    have hcomm := Subgroup.mem_centralizer_iff.1 (hQsyl.le hq) k hk
    rw [← map_mul, ← map_mul, hcomm]
  have hQ2' : IsPGroup 2 (Q.map ι) :=
    hQsyl.isPGroup.of_surjective (ι.subgroupMap Q) (ι.subgroupMap_surjective Q)
  have hQ4' : 4 ≤ Nat.card ↥(Q.map ι) := by
    rw [← Nat.card_congr (Q.equivMapOfInjective ι hι).toEquiv]
    exact hQ4
  have hterm' : Terminal ι.range (K.map ι) :=
    terminal_map ι hι hNA K (fun y hy2 hyc =>
      (hterm y hy2 (Subgroup.mem_centralizer_iff.2 fun k hk => hyc k hk)).2.2)
  let CN : Subgroup N := Subgroup.centralizer ({b} : Set N)
  let CL : Subgroup N := CN ⊓ L
  have hbc : b ∈ centralizer (K : Set N) := hQsyl.le hbQ
  have hcompN : IsCompIn CN K := hterm b hb2 hbc
  have hKCN : K ≤ CN := hcompN.1
  have hKCL : K ≤ CL := le_inf hKCN hKL
  have hsubCL : (K.subgroupOf CL).IsSubnormal :=
    CFSG.GroupTheory.isSubnormal_subgroupOf_of_le (B := K) (L := CL) (K := CN)
      inf_le_left hcompN.2.2
  have h2K : 2 ∣ Nat.card ↥K := by
    have hd : 2 ∣ Nat.card (↥K ⧸ pPrimeCore 2 ↥K) := by
      rw [hcard7]
      norm_num
    exact dvd_trans hd hdvd
  have h2qK : IsTwoQuasisimple ↥K :=
    (CFSG.ComponentClassification.HarrisLit.P1.isTwoQuasisimple_of_isQuasisimple hKq h2K).1
  have hsrc : IsTwoComponentIn K CL := ⟨hKCL, hsubCL, h2qK⟩
  have himg := L35.isTwoComponentIn_map_of_injective ι hι hsrc
  have hmapCL : CL.map ι =
      Subgroup.centralizer ({ι b} : Set (Perm (Fin n))) ⊓ alternatingGroup (Fin n) := by
    ext y
    constructor
    · rintro ⟨a, ⟨haC, haL⟩, rfl⟩
      have haC' : a * b = b * a := Subgroup.mem_centralizer_singleton_iff.mp haC
      refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_, ?_⟩
      · change ι a * ι b = ι b * ι a
        rw [← map_mul, ← map_mul, haC']
      · rw [hιL ⟨a, haL⟩]
        exact (e ⟨a, haL⟩).2
    · rintro ⟨hyC, hyA⟩
      let l : ↥L := e.symm ⟨y, hyA⟩
      have hyl : ((e l : alternatingGroup (Fin n)) : Perm (Fin n)) = y := by simp [l]
      refine ⟨(l : N), ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_, l.2⟩, ?_⟩
      · apply hι
        change ι ((l : N) * b) = ι (b * (l : N))
        rw [map_mul, map_mul, hιL l, hyl]
        exact Subgroup.mem_centralizer_singleton_iff.mp hyC
      · rw [hιL l, hyl]
  have hcomp' : IsTwoComponentIn (K.map ι)
      (Subgroup.centralizer ({ι b} : Set (Perm (Fin n))) ⊓ alternatingGroup (Fin n)) := by
    rwa [hmapCL] at himg
  have hbsq : b * b = 1 := by
    rw [← pow_two, ← hb2]
    exact pow_orderOf_eq_one b
  have hbQ' : ι b ∈ Q.map ι := Subgroup.mem_map_of_mem ι hbQ
  have hb2' : ι b * ι b = 1 := by rw [← map_mul, hbsq, map_one]
  obtain ⟨hQel', hQcard', hn11, hNalt⟩ :=
    alt_a7_perm_of_card hNA (K := K.map ι) (Q := Q.map ι) hK7' hQN' hQK' hQ2'
      hQ4' hterm' hbQ' hb2' hcomp'
  refine ⟨?_, ?_, hn11, ?_⟩
  · exact CFSG.IsElementaryAbelian.of_mulEquiv (Q.equivMapOfInjective ι hι).symm hQel'
  · exact (Nat.card_congr (Q.equivMapOfInjective ι hι).toEquiv).trans hQcard'
  ·
    have hLmap : L.map ι = alternatingGroup (Fin n) := by
      ext y
      constructor
      · rintro ⟨l, hl, rfl⟩
        rw [hιL ⟨l, hl⟩]
        exact (e ⟨l, hl⟩).2
      · intro hy
        refine ⟨(e.symm ⟨y, hy⟩ : ↥L), (e.symm ⟨y, hy⟩).2, ?_⟩
        rw [hιL]
        simp
    rw [eq_top_iff]
    intro n₀ _
    have hn₀ : ι n₀ ∈ alternatingGroup (Fin n) := hNalt ⟨n₀, rfl⟩
    have hn₀' : ι n₀ ∈ L.map ι := by rwa [hLmap]
    obtain ⟨l, hl, hlι⟩ := Subgroup.mem_map.mp hn₀'
    have hln : l = n₀ := hι hlι
    rwa [← hln]

theorem ivk73_a7_alt {n : ℕ} (N : Type) [Group N] [Finite N]
    (L K Q : Subgroup N) (hLnorm : L.Normal)
    (hcent : ∀ x : N, (∀ l ∈ L, x * l = l * x) → x = 1)
    (e : ↥L ≃* alternatingGroup (Fin n))
    (hKL : K ≤ L) (hKq : IsQuasisimple ↥K)
    (eK7 : (↥K ⧸ pPrimeCore 2 ↥K) ≃* alternatingGroup (Fin 7))
    (hQsyl : IsSylowOf 2 Q (centralizer (K : Set N)))
    (hQrank : 2 ≤ CFSG.pRank 2 ↥Q)
    (hterm : ∀ y : N, orderOf y = 2 → y ∈ centralizer (K : Set N) →
      IsCompIn (centralizer ({y} : Set N)) K) :
    IsElementaryAbelian 2 ↥Q ∧ Nat.card ↥Q = 4 ∧ n = 11 ∧ L = ⊤ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hrankOpen : 2 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup ↥Q) := by
    rw [← CFSG.SectionRank.pRank_eq_open_pRank_top]
    exact hQrank
  obtain ⟨E, -, hEel, hEcard⟩ :=
    CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := 2) (k := 2) hrankOpen
  have hE4 : Nat.card E = 4 := by rw [hEcard]; norm_num
  have hEne : E ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hE4
    omega
  obtain ⟨bE, hbEne⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hEne
  let b : N := (bE : ↥Q)
  have hbQ : b ∈ Q := (bE : ↥Q).2
  have hbsq : b * b = 1 := by
    have h := congrArg Subtype.val (hEel.2 bE bE.2)
    simpa [b, pow_two] using h
  have hb1 : b ≠ 1 := by
    intro h
    apply hbEne
    apply Subtype.ext
    apply Subtype.ext
    exact h
  have hb2 : orderOf b = 2 := orderOf_eq_prime (by rwa [pow_two]) hb1
  have hQ4 : 4 ≤ Nat.card ↥Q := by
    calc 4 = Nat.card E := hE4.symm
      _ ≤ Nat.card ↥Q := Subgroup.card_le_card_group E
  exact ivk73_a7_alt_of_b N L K Q hLnorm hcent e hKL hKq eK7 hQsyl
    b hbQ hb2 hQ4 hterm

end CFSG.GH74.GLS.IVK
