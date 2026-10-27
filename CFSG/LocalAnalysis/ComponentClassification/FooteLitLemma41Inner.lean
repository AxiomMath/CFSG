module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bAction
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCoprime
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitL2Facts

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.GSThmB
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem oddBarConj_eq_conj' {L : Subgroup G} (k : L) (hk : (k : G) ∈ normalizer (L : Set G)) :
    oddBarConj L ⟨k, hk⟩ = MulAut.conj (k : L ⧸ pPrimeCore 2 L) := by
  ext y
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
  rw [oddBarConj_apply_mk, MulAut.conj_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
    ← QuotientGroup.mk_mul]
  rfl

theorem commutator_le_coreActionKernel_of_le_inner (hAb : FooteL2AbelianCore)
    {J Y X : Subgroup G} {a : G} (hJq : IsQuasisimple (J ⧸ pPrimeCore 2 J))
    (hS : ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
      Blueprint.LieModel (J ⧸ pPrimeCore 2 J) .PSL 2 p f)
    (hYN : Y ≤ normalizer (J : Set G)) (haN : a ∈ normalizer (J : Set G)) (ha2 : a * a = 1)
    (haJ : a ∉ coreActionKernel J) (hYa : Y ≤ centralizer ({a} : Set G))
    (hYodd : Odd (Nat.card Y)) (hCY : ∀ k ∈ J, k * a = a * k → k ∈ normalizer (Y : Set G))
    (hXY : X ≤ Y)
    (hXinn : ∀ x (hx : x ∈ X), ∃ s : J ⧸ pPrimeCore 2 J,
      oddBarConj J ⟨x, hYN (hXY hx)⟩ = MulAut.conj s) :
    ⁅X, X⁆ ≤ coreActionKernel J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨p, f, hp, hp2, hf, hL⟩ := hS
  set S := J ⧸ pPrimeCore 2 J with hSdef
  set N := normalizer (J : Set G) with hNdef
  set ρ := oddBarConj J with hρ
  have hsimple : IsSimpleGroup S := isSimpleGroup_of_lieModel_psl_two hL
  have hZ : center S = ⊥ := center_eq_bot_of_isSimpleGroup (exists_mul_ne_mul_of_isQuasisimple hJq)
  have hinj : Function.Injective (MulAut.conj : S →* MulAut S) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro s hs
    have hsZ : s ∈ center S := by
      rw [mem_center_iff]
      intro g
      have h1 := DFunLike.congr_fun (MonoidHom.mem_ker.mp hs) g
      rw [MulAut.conj_apply, MulAut.one_apply] at h1
      calc g * s = s * g * s⁻¹ * s := by rw [h1]
        _ = s * g := by group
    rw [hZ] at hsZ
    exact hsZ
  set a' : N := ⟨a, haN⟩ with ha'
  set ρY := (Y.subgroupOf N).map ρ with hρY
  set T := ρY.comap (MulAut.conj : S →* MulAut S) with hT
  set C := MonoidHom.eqLocus (ρ a').toMonoidHom (MonoidHom.id S) with hC
  have ha'2 : orderOf (ρ a') = 2 := by
    apply orderOf_eq_prime
    · rw [← map_pow, sq]
      have : a' * a' = 1 := Subtype.ext ha2
      rw [this, map_one]
    · intro h
      exact haJ (mem_coreActionKernel_of_oddBarConj_eq_one h)
  have hconjφ : ∀ (φ : MulAut S) (s : S), MulAut.conj (φ s) = φ * MulAut.conj s * φ⁻¹ := by
    intro φ s
    ext g
    simp only [MulAut.conj_apply, MulAut.mul_apply, map_mul, map_inv, MulAut.apply_inv_self]
  have hTC : T ≤ C := by
    intro s hs
    obtain ⟨⟨y, hyN⟩, hyY, hys⟩ := mem_map.mp hs
    have hyY' : y ∈ Y := hyY
    have hya : (⟨y, hyN⟩ : N) * a' = a' * ⟨y, hyN⟩ :=
      Subtype.ext (mem_centralizer_singleton_iff.mp (hYa hyY'))
    have h1 : ρ a' * ρ ⟨y, hyN⟩ * (ρ a')⁻¹ = ρ ⟨y, hyN⟩ := by
      rw [← map_mul, ← hya, map_mul, mul_inv_cancel_right]
    have h2 : MulAut.conj (ρ a' s) = MulAut.conj s := by
      rw [hconjφ, ← hys, h1]
    show (ρ a') s = s
    exact hinj h2
  have hTodd : Odd (Nat.card T) := by
    have h1 : Nat.card T = Nat.card (T.map (MulAut.conj : S →* MulAut S)) :=
      (Subgroup.card_map_of_injective hinj).symm
    have h2 : T.map (MulAut.conj : S →* MulAut S) ≤ ρY := Subgroup.map_comap_le _ _
    have h3 : Nat.card ρY ∣ Nat.card Y := by
      rw [hρY]
      refine (Subgroup.card_map_dvd _ _).trans ?_
      rw [Nat.card_congr (subgroupOfEquivOfLe hYN).toEquiv]
    rw [h1]
    exact Odd.of_dvd_nat hYodd ((Subgroup.card_dvd_of_le h2).trans h3)
  have hTnorm : (T.subgroupOf C).Normal := by
    refine ⟨fun t ht c => ?_⟩
    obtain ⟨c, hcC⟩ := c
    obtain ⟨y0, rfl⟩ := QuotientGroup.mk_surjective c
    have hfix : oddBarConj J a' (y0 : S) = y0 := hcC
    obtain ⟨y', hy'c, hy'a⟩ := GSThmB.exists_fixed_lift (L := J) (t := a') ha2 hfix
    have hy'N : (y' : G) ∈ N := le_normalizer y'.2
    have hy'Y : (y' : G) ∈ normalizer (Y : Set G) := hCY y' y'.2 hy'a.symm
    have hconjc : MulAut.conj ((y0 : J) : S) = ρ ⟨y', hy'N⟩ := by
      rw [oddBarConj_eq_conj' y' hy'N, hy'c]
    have ht' : (t : S) ∈ T := ht
    obtain ⟨⟨y₁, hy₁N⟩, hy₁Y, hy₁t⟩ := mem_map.mp ht'
    have hy₁Y' : y₁ ∈ Y := hy₁Y
    show (((⟨(y0 : S), hcC⟩ : C) * t * (⟨(y0 : S), hcC⟩ : C)⁻¹ : C) : S) ∈ T
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    show MulAut.conj ((y0 : S) * (t : S) * (y0 : S)⁻¹) ∈ ρY
    rw [map_mul, map_mul, map_inv, hconjc, ← hy₁t, ← map_inv, ← map_mul, ← map_mul]
    refine mem_map_of_mem _ ?_
    show (y' : G) * y₁ * (y' : G)⁻¹ ∈ Y
    exact (mem_normalizer_iff.mp hy'Y y₁).mp hy₁Y'
  have hTO : T.subgroupOf C ≤ pPrimeCore 2 C := by
    refine le_sSup ⟨hTnorm, ?_⟩
    rw [Nat.card_congr (subgroupOfEquivOfLe hTC).toEquiv]
    exact Nat.coprime_two_left.mpr hTodd
  have hTcomm : ∀ s ∈ T, ∀ t ∈ T, s * t = t * s := by
    intro s hs t ht
    have h := hAb S p f hp hp2 hf hL (ρ a') ha'2 ⟨⟨s, hTC hs⟩, hTO hs⟩ ⟨⟨t, hTC ht⟩, hTO ht⟩
    exact congrArg (fun z : ↥(pPrimeCore 2 ↥C) => ((z : C) : S)) h
  rw [commutator_le]
  intro x₁ hx₁ x₂ hx₂
  obtain ⟨s₁, hs₁⟩ := hXinn x₁ hx₁
  obtain ⟨s₂, hs₂⟩ := hXinn x₂ hx₂
  have hs₁T : s₁ ∈ T := by
    show MulAut.conj s₁ ∈ ρY
    rw [← hs₁]
    exact mem_map_of_mem _ (show x₁ ∈ Y from hXY hx₁)
  have hs₂T : s₂ ∈ T := by
    show MulAut.conj s₂ ∈ ρY
    rw [← hs₂]
    exact mem_map_of_mem _ (show x₂ ∈ Y from hXY hx₂)
  have h1 : ρ ⁅(⟨x₁, hYN (hXY hx₁)⟩ : N), ⟨x₂, hYN (hXY hx₂)⟩⁆ = 1 := by
    rw [map_commutatorElement, hs₁, hs₂, ← map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm.mpr (hTcomm s₁ hs₁T s₂ hs₂T), map_one]
  have h2 := mem_coreActionKernel_of_oddBarConj_eq_one h1
  simpa [commutatorElement_def] using h2

theorem commutator_le_coreActionKernel_of_inner (hOut : FooteL2OutAbelian)
    (hAb : FooteL2AbelianCore) {J Y : Subgroup G} {a w : G}
    (hJq : IsQuasisimple (J ⧸ pPrimeCore 2 J))
    (hS : ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
      Blueprint.LieModel (J ⧸ pPrimeCore 2 J) .PSL 2 p f)
    (hYN : Y ≤ normalizer (J : Set G)) (hwN : w ∈ normalizer (J : Set G))
    (haN : a ∈ normalizer (J : Set G)) (ha2 : a * a = 1) (haJ : a ∉ coreActionKernel J)
    (hYa : Y ≤ centralizer ({a} : Set G)) (hYodd : Odd (Nat.card Y))
    (hCY : ∀ k ∈ J, k * a = a * k → k ∈ normalizer (Y : Set G))
    (hwY : w ∈ normalizer (Y : Set G)) :
    ⁅⁅Y, zpowers w⁆, ⁅Y, zpowers w⁆⁆ ≤ coreActionKernel J := by
  obtain ⟨p, f, hp, hp2, hf, hL⟩ := id hS
  set S := J ⧸ pPrimeCore 2 J with hSdef
  set N := normalizer (J : Set G) with hNdef
  set ρ := oddBarConj J with hρ
  set Inn := (MulAut.conj : S →* MulAut S).range with hInn
  have hXY : ⁅Y, zpowers w⁆ ≤ Y := commutator_le_self_of_le_normalizer (zpowers_le.mpr hwY)
  have hXI : ⁅Y, zpowers w⁆ ≤ (Inn.comap ρ).map N.subtype := by
    rw [commutator_le]
    intro y hy u hu
    have huN : u ∈ N := (zpowers_le.mpr hwN) hu
    refine ⟨⁅(⟨y, hYN hy⟩ : N), ⟨u, huN⟩⁆, ?_, ?_⟩
    · show ρ ⁅(⟨y, hYN hy⟩ : N), ⟨u, huN⟩⁆ ∈ Inn
      rw [map_commutatorElement, commutatorElement_def]
      obtain ⟨s, hs⟩ := hOut S p f hp hp2 hf hL (ρ ⟨y, hYN hy⟩) (ρ ⟨u, huN⟩)
      exact ⟨s, hs.symm⟩
    · simp [commutatorElement_def]
  refine commutator_le_coreActionKernel_of_le_inner hAb hJq hS hYN haN ha2 haJ hYa hYodd hCY hXY
    fun x hx => ?_
  obtain ⟨n, hn, rfl⟩ := mem_map.mp (hXI hx)
  obtain ⟨s, hs⟩ := hn
  exact ⟨s, hs.symm⟩

theorem commutator_le_coreActionKernel_of_oddOuterInner (hAb : FooteL2AbelianCore)
    {J Y : Subgroup G} {a : G} (hJq : IsQuasisimple (J ⧸ pPrimeCore 2 J))
    (hS : ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
      Blueprint.LieModel (J ⧸ pPrimeCore 2 J) .PSL 2 p f)
    (hinn : OddOuterInner (J ⧸ pPrimeCore 2 J))
    (hYN : Y ≤ normalizer (J : Set G)) (haN : a ∈ normalizer (J : Set G)) (ha2 : a * a = 1)
    (haJ : a ∉ coreActionKernel J) (hYa : Y ≤ centralizer ({a} : Set G))
    (hYodd : Odd (Nat.card Y)) (hCY : ∀ k ∈ J, k * a = a * k → k ∈ normalizer (Y : Set G)) :
    ⁅Y, Y⁆ ≤ coreActionKernel J := by
  refine commutator_le_coreActionKernel_of_le_inner hAb hJq hS hYN haN ha2 haJ hYa hYodd hCY
    le_rfl fun y hy => hinn _ ?_
  have h1 : orderOf (oddBarConj J ⟨y, hYN hy⟩) ∣ orderOf y := by
    have := orderOf_map_dvd (oddBarConj J) (⟨y, hYN hy⟩ : ↥(normalizer (J : Set G)))
    rwa [Subgroup.orderOf_mk] at this
  exact Odd.of_dvd_nat (odd_orderOf_of_mem_of_odd hYodd hy) h1

end CFSG.ComponentClassification.FooteLit
