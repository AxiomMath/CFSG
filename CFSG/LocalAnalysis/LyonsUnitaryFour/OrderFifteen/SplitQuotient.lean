module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.OrderFifteen.CoreFree

public section

namespace CFSG.LyonsUnitaryFour

open CFSG.RankTwoShapes

section Helpers

theorem nonempty_mulEquiv_elementarySixteen {P : Type*} [Group P] [Finite P]
    (hcard : Nat.card P = 16) (hcomm : ∀ x y : P, x * y = y * x) (hsq : ∀ x : P, x * x = 1) :
    Nonempty (P ≃* Multiplicative (Fin 4 → ZMod 2)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : CommGroup P := { (inferInstance : Group P) with mul_comm := hcomm }
  let _ : Module (ZMod 2) (Additive P) := AddCommGroup.zmodModule fun x => by
    rw [two_nsmul]
    exact hsq (Additive.toMul x)
  let _ : Fintype (Additive P) := Fintype.ofFinite _
  have : Module.Finite (ZMod 2) (Additive P) := Module.Finite.of_finite
  have hrank : Module.finrank (ZMod 2) (Additive P) = 4 := by
    have h := Module.card_eq_pow_finrank (K := ZMod 2) (V := Additive P)
    rw [ZMod.card, ← Nat.card_eq_fintype_card] at h
    change Nat.card P = _ at h
    rw [hcard] at h
    have h' : 2 ^ Module.finrank (ZMod 2) (Additive P) = 2 ^ 4 := by rw [← h]; norm_num
    exact Nat.pow_right_injective le_rfl h'
  have hrank' : Module.finrank (ZMod 2) (Fin 4 → ZMod 2) = 4 := Module.finrank_fin_fun _
  let f : Additive P ≃ₗ[ZMod 2] (Fin 4 → ZMod 2) :=
    LinearEquiv.ofFinrankEq _ _ (hrank.trans hrank'.symm)
  exact ⟨MulEquiv.toAdditiveLeft.symm f.toAddEquiv⟩

theorem card_modEq_one_of_fixedPointFree {Q : Type*} [Group Q] [Finite Q] {A : Subgroup Q}
    {g : Q} (hA : ∀ a ∈ A, g * a * g⁻¹ ∈ A) (h5 : ∀ a ∈ A, g ^ 5 * a * (g ^ 5)⁻¹ = a)
    (hfix : ∀ a ∈ A, g * a * g⁻¹ = a → a = 1) : Nat.card A ≡ 1 [MOD 5] := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let _ : Fintype A := Fintype.ofFinite _
  let f : Function.End A := fun a => ⟨g * a * g⁻¹, hA a a.2⟩
  have hiter : ∀ (n : ℕ) (a : A), ((f ^ n) a : Q) = g ^ n * a * (g ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro a; simp; rfl
    | succ n ih =>
      intro a
      change ((f^[n + 1]) a : Q) = _
      rw [Function.iterate_succ_apply']
      change g * ((f^[n]) a : Q) * g⁻¹ = _
      rw [show ((f^[n]) a : Q) = ((f ^ n) a : Q) from rfl, ih, pow_succ']
      group
  have hf5 : f ^ 5 ^ 1 = 1 := by
    funext a
    apply Subtype.ext
    rw [pow_one, hiter, h5 a a.2]
    rfl
  have hmod := Equiv.Perm.card_fixedPoints_modEq hf5
  have hfp : Fintype.card f.fixedPoints = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨1, Subtype.ext (by simp [f])⟩, ?_⟩
    rintro ⟨a, ha⟩
    apply Subtype.ext
    apply Subtype.ext
    have ha' : g * a * g⁻¹ = a := congrArg Subtype.val ha
    exact hfix a a.2 ha'
  rw [hfp, ← Nat.card_eq_fintype_card] at hmod
  exact hmod

theorem eq_bot_or_eq_top_of_card_modEq {P : Type*} [Group P] [Finite P] (hcard : Nat.card P = 16)
    (A : Subgroup P) (hA : Nat.card A ≡ 1 [MOD 5]) : A = ⊥ ∨ A = ⊤ := by
  have hdvd : Nat.card A ∣ 16 := hcard ▸ A.card_subgroup_dvd_card
  have hmem : Nat.card A ∈ Nat.divisors 16 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  have hdiv : Nat.divisors 16 = {1, 2, 4, 8, 16} := by decide
  rw [hdiv] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  unfold Nat.ModEq at hA
  rcases hmem with h | h | h | h | h
  · left
    exact Subgroup.eq_bot_of_card_eq A h
  · rw [h] at hA; norm_num at hA
  · rw [h] at hA; norm_num at hA
  · rw [h] at hA; norm_num at hA
  · right
    exact Subgroup.eq_top_of_card_eq A (h.trans hcard.symm)

variable {G : Type} [Group G]

theorem conj_mem_center_of_outer_order_five {K : Type} [Field K] {hK : Nat.card K = 16}
    (S : Subgroup G) (e : S.subgroupOf (Subgroup.normalizer (S : Set G)) ≃* unitaryFourW K hK)
    {n : G} (hn : n ∈ Subgroup.normalizer (S : Set G))
    (h5 : n ^ 5 ∈ S ⊔ Subgroup.centralizer (S : Set G))
    (h1 : n ∉ S ⊔ Subgroup.centralizer (S : Set G)) {s : G} (hs : s ∈ S)
    (hfix : n * s * n⁻¹ * s⁻¹ ∈ (Subgroup.center S).map S.subtype) :
    s ∈ (Subgroup.center S).map S.subtype := by
  have := charP_two_of_natCard_eq_sixteen hK
  have hnorm := Subgroup.normal_in_normalizer (H := S)
  set P := S.subgroupOf (Subgroup.normalizer (S : Set G)) with hP
  set α : MulAut P := MulAut.conjNormal (H := P) ⟨n, hn⟩ with hα
  have hker := ker_normalizerOuterAction S
  have hθ : ∀ m : Subgroup.normalizer (S : Set G),
      normalizerOuterAction S m = QuotientGroup.mk (MulAut.conjNormal (H := P) m) := fun m => rfl
  have hinn : ∀ m : Subgroup.normalizer (S : Set G),
      MulAut.conjNormal (H := P) m ∈ (MulAut.conj : P →* MulAut P).range ↔
        (m : G) ∈ S ⊔ Subgroup.centralizer (S : Set G) := by
    intro m
    rw [← Subgroup.mem_subgroupOf, ← hker, MonoidHom.mem_ker, hθ, QuotientGroup.eq_one_iff]
  have hα1 : α ∉ (MulAut.conj : P →* MulAut P).range := fun h => h1 ((hinn _).mp h)
  have hα5 : α ^ 5 ∈ (MulAut.conj : P →* MulAut P).range := by
    rw [hα, ← map_pow, hinn]
    exact h5
  set x : P := ⟨⟨s, Subgroup.le_normalizer hs⟩, hs⟩ with hx
  have hcomm : ∀ y : P, y * (α x * x⁻¹) = (α x * x⁻¹) * y := by
    intro y
    apply Subtype.ext
    apply Subtype.ext
    have hy : (((y : Subgroup.normalizer (S : Set G))) : G) ∈ S := y.2
    have h := (mem_map_center_iff.mp hfix).2 _ hy
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hα, MulAut.conjNormal_apply, hx]
    exact h
  have hcenter : α x * x⁻¹ ∈ Subgroup.center P :=
    Subgroup.mem_center_iff.mpr fun y => hcomm y
  have hW : e (α x * x⁻¹) ∈ Subgroup.center (unitaryFourW K hK) :=
    (mem_center_iff_of_mulEquiv e _).mpr hcenter
  rw [UnitaryFourW.center_eq_ker_firstCoord, UnitaryFourW.mem_ker_firstCoord, map_mul, map_inv,
    UnitaryFourW.fst_mul, UnitaryFourW.fst_inv] at hW
  have heq : UnitaryFourW.fst (e (α x)) = UnitaryFourW.fst (e x) :=
    CharTwo.add_eq_zero.mp hW
  have h0 := fst_eq_zero_of_outer_order_five e α hα5 hα1 x heq
  have hxW : e x ∈ Subgroup.center (unitaryFourW K hK) := by
    rw [UnitaryFourW.center_eq_ker_firstCoord, UnitaryFourW.mem_ker_firstCoord]
    exact h0
  have hxc : x ∈ Subgroup.center P := (mem_center_iff_of_mulEquiv e x).mp hxW
  refine mem_map_center_iff.mpr ⟨hs, fun t ht => ?_⟩
  have h := Subgroup.mem_center_iff.mp hxc ⟨⟨t, Subgroup.le_normalizer ht⟩, ht⟩
  exact congrArg (fun y : P => ((y : Subgroup.normalizer (S : Set G)) : G)) h

end Helpers

variable {G : Type} [Group G] [Finite G]

theorem lyons_order_fifteen_involution_centralizer_split_quotient
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) {T : Type} [Group T]
    (hT : CFSG.Assembly.LowTwoRank.StatedClassicalModel T .PSU 3 2 2) (S : Sylow 2 G)
    (U : Sylow 2 T) (hSU : Nonempty ((S : Subgroup G) ≃* (U : Subgroup T)))
    (hd : (((S : Subgroup G) ⊔ Subgroup.centralizer ((S : Subgroup G) : Set G)).subgroupOf
      (Subgroup.normalizer ((S : Subgroup G) : Set G))).index = 15)
    {z : G} (hzZ : z ∈ (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype)
    (hz1 : z ≠ 1) (S₀ : Subgroup (Subgroup.centralizer ({z} : Set G) ⧸
      CFSG.oddCore (Subgroup.centralizer ({z} : Set G))))
    (hS₀ : S₀ = ((S : Subgroup G).subgroupOf (Subgroup.centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (CFSG.oddCore (Subgroup.centralizer ({z} : Set G))))) :
    Odd (Nat.card (CFSG.oddCore (Subgroup.centralizer ({z} : Set G)))) ∧
    Function.Injective ((QuotientGroup.mk' (CFSG.oddCore (Subgroup.centralizer ({z} : Set G)))).comp
      ((S : Subgroup G).subgroupOf (Subgroup.centralizer ({z} : Set G))).subtype) ∧
    S₀.Normal ∧
    Nat.card (Subgroup.centralizer ({z} : Set G) ⧸
      CFSG.oddCore (Subgroup.centralizer ({z} : Set G))) = 320 ∧
    ∃ h : Subgroup.centralizer ({z} : Set G) ⧸ CFSG.oddCore (Subgroup.centralizer ({z} : Set G)),
      orderOf h = 5 ∧ S₀ ⊔ Subgroup.zpowers h = ⊤ ∧ S₀ ⊓ Subgroup.zpowers h = ⊥ ∧
      (Subgroup.center S₀).map S₀.subtype =
        (((Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype).subgroupOf
          (Subgroup.centralizer ({z} : Set G))).map
          (QuotientGroup.mk' (CFSG.oddCore (Subgroup.centralizer ({z} : Set G)))) ∧
      (∀ x ∈ (Subgroup.center S₀).map S₀.subtype, h * x * h⁻¹ = x) ∧
      (∀ x ∈ S₀, h * x * h⁻¹ * x⁻¹ ∈ (Subgroup.center S₀).map S₀.subtype →
        x ∈ (Subgroup.center S₀).map S₀.subtype) ∧
      QuotientGroup.mk' (CFSG.oddCore (Subgroup.centralizer ({z} : Set G)))
          ⟨z, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ ∈
        (Subgroup.center S₀).map S₀.subtype ∧
      QuotientGroup.mk' (CFSG.oddCore (Subgroup.centralizer ({z} : Set G)))
          ⟨z, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ ≠ 1 := by
  classical
  subst hS₀
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hcard64, hZcomm, -, hZcard, hZexp, -, -, -, -, -, -, hloc⟩ :=
    lyons_unitary_four_fusion_and_centralizers hnonab hT S U hSU
  obtain ⟨-, -, -, hMfacts⟩ := lyons_unitary_four_normalizer_odd_quotient hnonab hT S U hSU
  obtain ⟨-, -, hRM, -, -, hidxM, -⟩ := hMfacts z hzZ hz1
  rw [hd, show (15 : ℕ) / 3 = 5 from rfl] at hidxM
  obtain ⟨-, -, -, hsqZ, -⟩ := unitary_four_sylow_structure hT S U hSU
  set Sg := (S : Subgroup G) with hSg
  set N := Subgroup.normalizer (Sg : Set G) with hN
  set Cs := Subgroup.centralizer (Sg : Set G) with hCs
  set R := Sg ⊔ Cs with hR
  set Z := (Subgroup.center Sg).map Sg.subtype with hZ
  set C := Subgroup.centralizer ({z} : Set G) with hC
  set K := CFSG.oddCore C with hK
  have hZS : ∀ w ∈ Z, w ∈ Sg := fun w hw => (mem_map_center_iff.mp hw).1
  have hZcardG : Nat.card Z = 4 := by
    rw [hZ, Subgroup.card_map_of_injective Sg.subtype_injective, hZcard]
  have hSC : Sg ≤ C := fun s hs =>
    Subgroup.mem_centralizer_singleton_iff.mpr ((mem_map_center_iff.mp hzZ).2 s hs)
  have hsqZG : ∀ s ∈ Sg, s * s ∈ Z := by
    intro s hs
    refine ⟨⟨s, hs⟩ ^ 2, hsqZ ⟨s, hs⟩, ?_⟩
    simp [pow_two]
  have hZexpG : ∀ w ∈ Z, w * w = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    have h := congrArg Subtype.val (hZexp y hy)
    simpa [pow_two] using h
  have hcommZ : ∀ s ∈ Sg, ∀ t ∈ Sg, s * t * s⁻¹ * t⁻¹ ∈ Z := by
    intro s hs t ht
    rw [hZcomm]
    simpa [commutatorElement_def] using Subgroup.commutator_mem_commutator hs ht
  have hRtriv : ∀ r ∈ R, ∀ s ∈ Sg, r * s * r⁻¹ * s⁻¹ ∈ Z := by
    intro r hr s hs
    have hr' : r ∈ ((Sg ⊔ Cs : Subgroup G) : Set G) := hr
    rw [Subgroup.coe_mul_of_left_le_normalizer_right Sg _ (le_normalizer_centralizer Sg),
      Set.mem_mul] at hr'
    obtain ⟨s₀, hs₀, c, hc, rfl⟩ := hr'
    have hcs : c * s = s * c := (Subgroup.mem_centralizer_iff.mp hc s hs).symm
    have h : s₀ * c * s * (s₀ * c)⁻¹ * s⁻¹ = s₀ * s * s₀⁻¹ * s⁻¹ := by
      calc s₀ * c * s * (s₀ * c)⁻¹ * s⁻¹ = s₀ * (c * s) * c⁻¹ * s₀⁻¹ * s⁻¹ := by group
        _ = s₀ * (s * c) * c⁻¹ * s₀⁻¹ * s⁻¹ := by rw [hcs]
        _ = s₀ * s * s₀⁻¹ * s⁻¹ := by group
    rw [h]
    exact hcommZ s₀ hs₀ s hs
  have hGF : Nat.card (GaloisField 2 4) = 16 := by
    rw [GaloisField.card 2 4 (by norm_num)]
    norm_num
  obtain ⟨eU⟩ := nonempty_sylow_equiv_unitaryFourW hT U (GaloisField 2 4) hGF
  let e : Sg.subgroupOf N ≃* unitaryFourW (GaloisField 2 4) hGF :=
    (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer).trans (hSU.some.trans eU)
  set M := N ⊓ C with hM
  have hM5 : ∀ m ∈ M, m ^ 5 ∈ R := by
    intro m hm
    have hcardMR : Nat.card (M ⧸ R.subgroupOf M) = 5 := hidxM
    have h := pow_card_eq_one' (G := M ⧸ R.subgroupOf M)
      (x := ((⟨m, hm⟩ : M) : M ⧸ R.subgroupOf M))
    rw [hcardMR, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf] at h
    simpa using h
  have hfpf : ∀ m ∈ M, m ∉ R → ∀ s ∈ Sg, m * s * m⁻¹ * s⁻¹ ∈ Z → s ∈ Z :=
    fun m hm hmR s hs hfix =>
      conj_mem_center_of_outer_order_five Sg e hm.1 (hM5 m hm) hmR hs hfix
  obtain ⟨m₀, hm₀M, hm₀R⟩ : ∃ m ∈ M, m ∉ R := by
    by_contra hall
    push Not at hall
    have htop : R.subgroupOf M = ⊤ :=
      eq_top_iff.mpr fun x _ => Subgroup.mem_subgroupOf.mpr (hall x x.2)
    rw [htop, Subgroup.index_top] at hidxM
    norm_num at hidxM
  set SC : Subgroup C := Sg.subgroupOf C with hSCdef
  set ZC : Subgroup C := Z.subgroupOf C with hZCdef
  have hZCSC : ZC ≤ SC := by
    intro w hw
    rw [hZCdef, Subgroup.mem_subgroupOf] at hw
    rw [hSCdef, Subgroup.mem_subgroupOf]
    exact hZS _ hw
  have hSK1 : ∀ k : C, k ∈ K → (k : G) ∈ Sg → k = 1 := by
    intro k hk hkS
    have hodd : Odd (orderOf k) := CFSG.Adapters.odd_orderOf_of_mem_oddCore hk
    obtain ⟨j, hj⟩ := S.isPGroup' ⟨(k : G), hkS⟩
    have hdvd : orderOf k ∣ 2 ^ j := by
      apply orderOf_dvd_of_pow_eq_one
      apply Subtype.ext
      have := congrArg Subtype.val hj
      simpa using this
    have hcop : Nat.Coprime (orderOf k) (2 ^ j) :=
      (Nat.coprime_two_right.mpr hodd).pow_right j
    exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop hdvd)
  set πK := QuotientGroup.mk' K with hπKdef
  set S₀ := SC.map πK with hS₀
  have hπK : Function.Surjective πK := QuotientGroup.mk'_surjective K
  have hπKinj : ∀ x ∈ SC, ∀ y ∈ SC, πK x = πK y → x = y := by
    intro x hx y hy hxy
    rw [hπKdef, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hxy
    have h1 := hSK1 _ hxy (by
      have := SC.mul_mem (SC.inv_mem hx) hy
      rw [hSCdef, Subgroup.mem_subgroupOf] at this
      exact this)
    calc x = x * (x⁻¹ * y) := by rw [h1, mul_one]
      _ = y := by group
  set E : Subgroup (C ⧸ K) := ZC.map πK with hEdef
  have hEc : E ≤ Subgroup.center (C ⧸ K) := (hloc z hzZ hz1).2.2
  have hEn : E.Normal := by
    refine ⟨fun a ha g => ?_⟩
    rw [Subgroup.mem_center_iff.mp (hEc ha) g, mul_inv_cancel_right]
    exact ha
  have hZCp : IsPGroup 2 ZC := by
    have hZp : IsPGroup 2 Z := S.isPGroup'.to_le (fun w hw => hZS w hw)
    exact hZp.of_equiv (Subgroup.subgroupOfEquivOfLe (fun w hw => hSC (hZS w hw))).symm
  have hE2 : IsPGroup 2 E := hZCp.map πK
  set πE := QuotientGroup.mk' E with hπEdef
  have hπE : Function.Surjective πE := QuotientGroup.mk'_surjective E
  set π : C →* (C ⧸ K) ⧸ E := πE.comp πK with hπdef
  have hπ : Function.Surjective π := hπE.comp hπK
  have hcore : CFSG.oddCore ((C ⧸ K) ⧸ E) = ⊥ := by
    obtain ⟨hmap, -, -⟩ := oddCore_quotient_central_two E hEc hE2
    rw [← hmap, oddCore_quotient_oddCore_eq_bot, Subgroup.map_bot]
  have hπker : ∀ x y : C, π x = π y → ∃ w ∈ ZC, ∃ k ∈ K, y = x * w * k := by
    intro x y hxy
    have h1 : (πK x)⁻¹ * πK y ∈ E := by
      have := QuotientGroup.eq.mp (show (QuotientGroup.mk (πK x) : (C ⧸ K) ⧸ E) =
        QuotientGroup.mk (πK y) from hxy)
      exact this
    obtain ⟨w, hw, hwe⟩ := h1
    refine ⟨w, hw, (x * w)⁻¹ * y, ?_, by group⟩
    have h2 : πK (x * w) = πK y := by
      rw [map_mul, hwe, mul_inv_cancel_left]
    rw [hπKdef, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h2
    exact h2
  have hπZC : ∀ w ∈ ZC, π w = 1 := by
    intro w hw
    rw [hπdef, MonoidHom.comp_apply, hπEdef, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact ⟨w, hw, rfl⟩
  have hπK1 : ∀ k ∈ K, π k = 1 := by
    intro k hk
    show πE (πK k) = 1
    rw [show πK k = 1 from (QuotientGroup.eq_one_iff k).mpr hk, map_one]
  have hkerS : ∀ s ∈ SC, π s = 1 → (s : G) ∈ Z := by
    intro s hs h1
    obtain ⟨w, hw, k, hk, hsk⟩ := hπker 1 s (by rw [map_one, h1])
    rw [one_mul] at hsk
    have hkS : ((w⁻¹ * s : C) : G) ∈ Sg := by
      have := SC.mul_mem (SC.inv_mem (hZCSC hw)) hs
      rw [hSCdef, Subgroup.mem_subgroupOf] at this
      exact this
    have hk' : k = w⁻¹ * s := by rw [hsk]; group
    have hk1 := hSK1 k hk (hk' ▸ hkS)
    rw [hk1, mul_one] at hsk
    rw [hsk]
    exact (Subgroup.mem_subgroupOf).mp hw
  set SCs : Sylow 2 C := S.subtype hSC with hSCs
  have hSCs_coe : (SCs : Subgroup C) = SC := Sylow.coe_subtype _ _
  set Pbar : Sylow 2 ((C ⧸ K) ⧸ E) := SCs.mapSurjective hπ with hPbardef
  have hmemPbar : ∀ y, y ∈ (Pbar : Subgroup ((C ⧸ K) ⧸ E)) ↔ ∃ s ∈ SC, π s = y := by
    intro y
    rw [hPbardef, Sylow.coe_mapSurjective, Subgroup.mem_map, hSCs_coe]
  have hPbar_comm : ∀ s ∈ SC, ∀ s' ∈ SC, π s * π s' = π s' * π s := by
    intro s hs s' hs'
    have hcomm : s * s' * s⁻¹ * s'⁻¹ ∈ ZC := by
      rw [hZCdef, Subgroup.mem_subgroupOf]
      simpa using hcommZ _ (Subgroup.mem_subgroupOf.mp hs) _ (Subgroup.mem_subgroupOf.mp hs')
    have h1 := hπZC _ hcomm
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    calc π s * π s' = (π s * π s' * (π s)⁻¹ * (π s')⁻¹) * (π s' * π s) := by group
      _ = π s' * π s := by rw [h1, one_mul]
  have hPbar_sq : ∀ s ∈ SC, π s * π s = 1 := by
    intro s hs
    rw [← map_mul]
    apply hπZC
    rw [hZCdef, Subgroup.mem_subgroupOf]
    simpa using hsqZG _ (Subgroup.mem_subgroupOf.mp hs)
  have hPbar_card : Nat.card (Pbar : Subgroup ((C ⧸ K) ⧸ E)) = 16 := by
    set φS : SC →* (C ⧸ K) ⧸ E := π.comp SC.subtype with hφS
    have hrange : φS.range = (Pbar : Subgroup ((C ⧸ K) ⧸ E)) := by
      ext y
      rw [hmemPbar, MonoidHom.mem_range]
      constructor
      · rintro ⟨s, rfl⟩
        exact ⟨s, s.2, rfl⟩
      · rintro ⟨s, hs, rfl⟩
        exact ⟨⟨s, hs⟩, rfl⟩
    have hker : φS.ker = ZC.subgroupOf SC := by
      ext s
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      constructor
      · intro h
        rw [hZCdef, Subgroup.mem_subgroupOf]
        exact hkerS s s.2 h
      · intro h
        exact hπZC _ h
    have hkercard : Nat.card φS.ker = 4 := by
      rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZCSC).toEquiv, hZCdef,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe (fun w hw => hSC (hZS w hw))).toEquiv,
        hZcardG]
    have hSCcard : Nat.card SC = 64 := by
      rw [hSCdef, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSC).toEquiv, hcard64]
    have h := φS.ker.card_mul_index
    rw [hkercard, Subgroup.index_ker, hrange, hSCcard] at h
    omega
  have hPbar_iso :
      Nonempty ((Pbar : Subgroup ((C ⧸ K) ⧸ E)) ≃* Multiplicative (Fin 4 → ZMod 2)) := by
    apply nonempty_mulEquiv_elementarySixteen hPbar_card
    · rintro ⟨x, hx⟩ ⟨y, hy⟩
      obtain ⟨s, hs, rfl⟩ := (hmemPbar x).mp hx
      obtain ⟨s', hs', rfl⟩ := (hmemPbar y).mp hy
      exact Subtype.ext (hPbar_comm s hs s' hs')
    · rintro ⟨x, hx⟩
      obtain ⟨s, hs, rfl⟩ := (hmemPbar x).mp hx
      exact Subtype.ext (hPbar_sq s hs)
  set Q := (C ⧸ K) ⧸ E with hQ
  set NQ := Subgroup.normalizer ((Pbar : Subgroup Q) : Set Q) with hNQ
  set CQ := Subgroup.centralizer ((Pbar : Subgroup Q) : Set Q) with hCQ
  have hSCconj : ∀ c : C, (c : G) ∈ N → ∀ s ∈ SC, c * s * c⁻¹ ∈ SC := by
    intro c hc s hs
    rw [hSCdef, Subgroup.mem_subgroupOf] at hs ⊢
    simpa using (Subgroup.mem_normalizer_iff.mp hc s).mp hs
  have hπN : ∀ c : C, (c : G) ∈ N → π c ∈ NQ := by
    intro c hc
    rw [hNQ, Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      obtain ⟨s, hs, rfl⟩ := (hmemPbar y).mp hy
      exact (hmemPbar _).mpr ⟨c * s * c⁻¹, hSCconj c hc s hs, by
        rw [map_mul, map_mul, map_inv]⟩
    · intro hy
      obtain ⟨s, hs, hseq⟩ := (hmemPbar _).mp hy
      have hc' : ((c⁻¹ : C) : G) ∈ N := by simpa using N.inv_mem hc
      refine (hmemPbar y).mpr ⟨c⁻¹ * s * c⁻¹⁻¹, hSCconj c⁻¹ hc' s hs, ?_⟩
      rw [inv_inv, map_mul, map_mul, map_inv, hseq]
      group
  have hNQ_mem : ∀ q ∈ NQ, ∃ s ∈ SC, ∃ m : C, (m : G) ∈ N ∧ q = (π s)⁻¹ * π m := by
    intro ybar hybar
    obtain ⟨c, rfl⟩ := hπ ybar
    have hA : ∀ s ∈ SC, c * s * c⁻¹ ∈ SC ⊔ K := by
      intro s hs
      have h1 : π (c * s * c⁻¹) ∈ (Pbar : Subgroup Q) := by
        rw [map_mul, map_mul, map_inv]
        exact (Subgroup.mem_normalizer_iff.mp hybar (π s)).mp ((hmemPbar _).mpr ⟨s, hs, rfl⟩)
      obtain ⟨s', hs', hs'eq⟩ := (hmemPbar _).mp h1
      obtain ⟨w, hw, k, hk, hrepr⟩ := hπker s' (c * s * c⁻¹) hs'eq
      rw [hrepr]
      exact Subgroup.mul_mem_sup (SC.mul_mem hs' (hZCSC hw)) hk
    have hSCK : (SCs : Subgroup C) ≤ SC ⊔ K := hSCs_coe ▸ le_sup_left
    have hQ' : SC.map (MulAut.conj c).toMonoidHom ≤ SC ⊔ K := by
      rintro _ ⟨s, hs, rfl⟩
      exact hA s hs
    have hQp : IsPGroup 2 (SC.map (MulAut.conj c).toMonoidHom) :=
      (hSCs_coe ▸ SCs.isPGroup').map _
    obtain ⟨v, hv, hvc⟩ := exists_conj_le_sylow_of_le SCs hSCK hQ' hQp
    set n := v * c with hndef
    have hnN : ∀ s ∈ SC, n * s * n⁻¹ ∈ SC := by
      intro s hs
      have := hvc (c * s * c⁻¹) ⟨s, hs, rfl⟩
      rw [hSCs_coe] at this
      convert this using 1
      rw [hndef]
      group
    have hnG : (n : G) ∈ N := by
      have hmap : Sg.map (MulAut.conj (n : G)).toMonoidHom = Sg := by
        apply Subgroup.eq_of_le_of_card_ge
        · rintro _ ⟨s, hs, rfl⟩
          have := hnN ⟨s, hSC hs⟩ (Subgroup.mem_subgroupOf.mpr hs)
          rw [Subgroup.mem_subgroupOf] at this
          simpa using this
        · rw [Subgroup.card_map_of_injective (MulAut.conj (n : G)).injective]
      exact mem_normalizer_of_map_conj_eq hmap
    have hv' : v ∈ ((SC ⊔ K : Subgroup C) : Set C) := hv
    rw [Subgroup.mul_normal, Set.mem_mul] at hv'
    obtain ⟨s₁, hs₁, k₁, hk₁, hv_eq⟩ := hv'
    refine ⟨s₁, hs₁, n, hnG, ?_⟩
    have hc_eq : c = v⁻¹ * n := by rw [hndef]; group
    rw [hc_eq, map_mul, map_inv, ← hv_eq, map_mul, hπK1 k₁ hk₁, mul_one]
  have hPCQ : (Pbar : Subgroup Q) ≤ CQ := by
    intro x hx
    rw [hCQ, Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨s, hs, rfl⟩ := (hmemPbar x).mp hx
    obtain ⟨s', hs', rfl⟩ := (hmemPbar y).mp hy
    exact hPbar_comm s' hs' s hs
  have hπC_iff : ∀ (m : G) (hm : m ∈ M), π ⟨m, hm.2⟩ ∈ CQ ↔ m ∈ R := by
    intro m hm
    constructor
    · intro hc
      by_contra hmR
      have hall : Sg ≤ Z := by
        intro s hs
        apply hfpf m hm hmR s hs
        set w : C := ⟨m, hm.2⟩ * ⟨s, hSC hs⟩ * ⟨m, hm.2⟩⁻¹ * ⟨s, hSC hs⟩⁻¹ with hw
        have hwS : w ∈ SC := SC.mul_mem (hSCconj _ hm.1 _ (Subgroup.mem_subgroupOf.mpr hs))
          (SC.inv_mem (Subgroup.mem_subgroupOf.mpr hs))
        have hw1 : π w = 1 := by
          have h1 := (Subgroup.mem_centralizer_iff.mp hc) (π ⟨s, hSC hs⟩)
            ((hmemPbar _).mpr ⟨_, Subgroup.mem_subgroupOf.mpr hs, rfl⟩)
          rw [hw, map_mul, map_mul, map_mul, map_inv, map_inv, ← h1]
          group
        simpa [hw] using hkerS w hwS hw1
      have hle := Subgroup.card_le_of_le hall
      rw [hcard64, hZcardG] at hle
      omega
    · intro hmR
      rw [hCQ, Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨s, hs, rfl⟩ := (hmemPbar y).mp hy
      set w : C := ⟨m, hm.2⟩ * s * ⟨m, hm.2⟩⁻¹ * s⁻¹ with hw
      have hwZ : w ∈ ZC := by
        rw [hZCdef, Subgroup.mem_subgroupOf]
        simpa [hw] using hRtriv m hmR s (Subgroup.mem_subgroupOf.mp hs)
      have hw1 := hπZC w hwZ
      have heq : (⟨m, hm.2⟩ : C) * s = w * s * ⟨m, hm.2⟩ := by rw [hw]; group
      calc π s * π ⟨m, hm.2⟩ = π w * π s * π ⟨m, hm.2⟩ := by rw [hw1, one_mul]
        _ = π ⟨m, hm.2⟩ * π s := by rw [← map_mul, ← map_mul, ← heq, map_mul]
  let ρ₀ : M →* NQ :=
    { toFun := fun m => ⟨π ⟨(m : G), m.2.2⟩, hπN _ m.2.1⟩
      map_one' := Subtype.ext (map_one π)
      map_mul' := fun a b => Subtype.ext (map_mul π ⟨(a : G), a.2.2⟩ ⟨(b : G), b.2.2⟩) }
  let ρ : M →* NQ ⧸ CQ.subgroupOf NQ := (QuotientGroup.mk' (CQ.subgroupOf NQ)).comp ρ₀
  have hρker : ρ.ker = R.subgroupOf M := by
    ext m
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    simp only [ρ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf]
    exact hπC_iff (m : G) m.2
  have hρsurj : Function.Surjective ρ := by
    rintro q
    obtain ⟨⟨q, hq⟩, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨s, hs, m₁, hm₁N, hqeq⟩ := hNQ_mem q hq
    refine ⟨⟨(m₁ : G), hm₁N, m₁.2⟩, ?_⟩
    simp only [ρ, MonoidHom.comp_apply, QuotientGroup.mk'_apply]
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    apply hPCQ
    have hm₁ : π m₁ ∈ NQ := hπN m₁ hm₁N
    have hinvN : (π m₁)⁻¹ ∈ NQ := NQ.inv_mem hm₁
    have hsP : (π s)⁻¹ ∈ (Pbar : Subgroup Q) :=
      Subgroup.inv_mem _ ((hmemPbar _).mpr ⟨s, hs, rfl⟩)
    have h := (Subgroup.mem_normalizer_iff.mp hinvN _).mp hsP
    change (π m₁)⁻¹ * q ∈ (Pbar : Subgroup Q)
    rw [hqeq]
    simpa [mul_assoc] using h
  have hidxQ : (CQ.subgroupOf NQ).index = 5 := by
    have e₁ := (QuotientGroup.quotientMulEquivOfEq hρker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ρ hρsurj)
    rw [Subgroup.index, ← Nat.card_congr e₁.toEquiv]
    exact hidxM
  have hirrQ : ∀ A : Subgroup Q, A ≤ (Pbar : Subgroup Q) →
      (∀ n ∈ NQ, ∀ a ∈ A, n * a * n⁻¹ ∈ A) → A = ⊥ ∨ A = (Pbar : Subgroup Q) := by
    intro A hAP hA
    set g := π ⟨m₀, hm₀M.2⟩ with hg
    have hgN : g ∈ NQ := hπN _ hm₀M.1
    have hAg : ∀ a ∈ A, g * a * g⁻¹ ∈ A := hA g hgN
    have hg5 : ∀ a ∈ A, g ^ 5 * a * (g ^ 5)⁻¹ = a := by
      intro a ha
      have hc : g ^ 5 ∈ CQ := by
        have h5eq : g ^ 5 = π ⟨m₀ ^ 5, (M.pow_mem hm₀M 5).2⟩ := by
          rw [hg, ← map_pow]
          rfl
        rw [h5eq]
        exact (hπC_iff _ (M.pow_mem hm₀M 5)).mpr (hM5 m₀ hm₀M)
      have h := (Subgroup.mem_centralizer_iff.mp hc) a (hAP ha)
      rw [← h]
      group
    have hgfix : ∀ a ∈ A, g * a * g⁻¹ = a → a = 1 := by
      intro a ha hga
      obtain ⟨s, hs, rfl⟩ := (hmemPbar a).mp (hAP ha)
      set w : C := ⟨m₀, hm₀M.2⟩ * s * ⟨m₀, hm₀M.2⟩⁻¹ * s⁻¹ with hw
      have hw1 : π w = 1 := by
        rw [hw, map_mul, map_mul, map_mul, map_inv, map_inv, ← hg, hga]
        group
      have hwS : w ∈ SC := SC.mul_mem (hSCconj _ hm₀M.1 s hs) (SC.inv_mem hs)
      have hwZ := hkerS w hwS hw1
      have hsZ := hfpf m₀ hm₀M hm₀R s (Subgroup.mem_subgroupOf.mp hs) (by simpa [hw] using hwZ)
      exact hπZC s (Subgroup.mem_subgroupOf.mpr hsZ)
    have hmod := card_modEq_one_of_fixedPointFree hAg hg5 hgfix
    have hA' := eq_bot_or_eq_top_of_card_modEq hPbar_card (A.subgroupOf Pbar)
      (by rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAP).toEquiv])
    rcases hA' with h | h
    · left
      rw [← Subgroup.map_subgroupOf_eq_of_le hAP, h, Subgroup.map_bot]
    · right
      rw [← Subgroup.map_subgroupOf_eq_of_le hAP, h, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype]
  obtain ⟨hPn, -, hcardQ, hb, hhb5, -, -, -, hfpfb⟩ :=
    core_free_elementary_sixteen_order_five_normal_sylow hcore Pbar hPbar_iso hidxQ hirrQ
  have hcard_map : ∀ H : Subgroup C, H ≤ SC → Nat.card (H.map πK) = Nat.card H := by
    intro H hH
    have hinj : Function.Injective (πK.comp H.subtype) := fun x y hxy =>
      Subtype.ext (hπKinj _ (hH x.2) _ (hH y.2) hxy)
    rw [show H.map πK = (πK.comp H.subtype).range by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hSCcard : Nat.card SC = 64 := by
    rw [hSCdef, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSC).toEquiv, hcard64]
  have hZCcard : Nat.card ZC = 4 := by
    rw [hZCdef, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (fun w hw => hSC (hZS w hw))).toEquiv,
      hZcardG]
  have hEcard : Nat.card E = 4 := by rw [hEdef, hcard_map ZC hZCSC, hZCcard]
  have hS₀card : Nat.card S₀ = 64 := by rw [hS₀, hcard_map SC le_rfl, hSCcard]
  have hLcard : Nat.card (C ⧸ K) = 320 := by
    rw [← E.card_mul_index, hEcard, Subgroup.index, ← hQ, hcardQ]
  have hES₀ : E ≤ S₀ := by
    rw [hS₀, hEdef]
    exact Subgroup.map_mono hZCSC
  have hPbar_eq : (Pbar : Subgroup Q) = S₀.map πE := by
    rw [hPbardef, Sylow.coe_mapSurjective, hSCs_coe, hS₀, Subgroup.map_map]
  have hS₀comap : S₀ = (Pbar : Subgroup Q).comap πE := by
    rw [hPbar_eq, Subgroup.comap_map_eq, hπEdef, QuotientGroup.ker_mk', sup_eq_left.mpr hES₀]
  have hS₀normal : S₀.Normal := by
    rw [hS₀comap]
    exact hPn.comap πE
  have hcenter : (Subgroup.center S₀).map S₀.subtype = E := by
    ext x
    rw [mem_map_center_iff]
    constructor
    · rintro ⟨hxS, hx⟩
      have hxS' := hxS
      rw [hS₀] at hxS'
      obtain ⟨s, hs, rfl⟩ := hxS'
      have hsZ : (s : G) ∈ Z := by
        refine mem_map_center_iff.mpr ⟨Subgroup.mem_subgroupOf.mp hs, fun t ht => ?_⟩
        have htSC : (⟨t, hSC ht⟩ : C) ∈ SC := Subgroup.mem_subgroupOf.mpr ht
        have h1 := hx (πK ⟨t, hSC ht⟩) (by rw [hS₀]; exact ⟨_, htSC, rfl⟩)
        rw [← map_mul, ← map_mul] at h1
        exact congrArg Subtype.val
          (hπKinj _ (SC.mul_mem htSC hs) _ (SC.mul_mem hs htSC) h1)
      exact ⟨s, Subgroup.mem_subgroupOf.mpr hsZ, rfl⟩
    · intro hx
      exact ⟨hES₀ hx, fun y _ => Subgroup.mem_center_iff.mp (hEc hx) y⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨hhat, hhat_eq⟩ := hπE hb
  have hhat5 : hhat ^ 5 ∈ E := by
    have h1 : πE (hhat ^ 5) = 1 := by rw [map_pow, hhat_eq, ← hhb5, pow_orderOf_eq_one]
    rw [hπEdef, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact h1
  have hhat10 : hhat ^ 10 = 1 := by
    obtain ⟨w, hw, hwe⟩ := hhat5
    have hw2 : w * w = 1 := Subtype.ext (hZexpG _ (Subgroup.mem_subgroupOf.mp hw))
    rw [show (10 : ℕ) = 5 * 2 from rfl, pow_mul, ← hwe, pow_two, ← map_mul, hw2, map_one]
  set h := hhat ^ 6 with hhdef
  have hh5 : h ^ 5 = 1 := by
    rw [hhdef, ← pow_mul, show (6 * 5 : ℕ) = 10 * 3 from rfl, pow_mul, hhat10, one_pow]
  have hπEh : πE h = hb := by
    rw [hhdef, map_pow, hhat_eq, show (6 : ℕ) = 5 + 1 from rfl, pow_succ, ← hhb5,
      pow_orderOf_eq_one, one_mul]
  have hh1 : h ≠ 1 := by
    intro h1
    have h2 := hπEh
    rw [h1, map_one] at h2
    rw [← h2, orderOf_one] at hhb5
    norm_num at hhb5
  have hhord : orderOf h = 5 := orderOf_eq_prime hh5 hh1
  have hS₀p : IsPGroup 2 S₀ := by
    rw [hS₀]
    exact (hSCs_coe ▸ SCs.isPGroup').map πK
  refine ⟨odd_card_oddCore C, fun x y hxy => Subtype.ext (hπKinj _ x.2 _ y.2 hxy),
    hS₀normal, hLcard, h, hhord, ?_, ?_, hcenter, ?_, ?_, ?_, ?_⟩
  · apply Subgroup.eq_top_of_card_eq
    have h64 : 64 ∣ Nat.card (S₀ ⊔ Subgroup.zpowers h : Subgroup (C ⧸ K)) :=
      hS₀card ▸ Subgroup.card_dvd_of_le le_sup_left
    have h5 : 5 ∣ Nat.card (S₀ ⊔ Subgroup.zpowers h : Subgroup (C ⧸ K)) := by
      have := Subgroup.card_dvd_of_le (le_sup_right : Subgroup.zpowers h ≤ S₀ ⊔ _)
      rwa [Nat.card_zpowers, hhord] at this
    have h320 : 320 ∣ Nat.card (S₀ ⊔ Subgroup.zpowers h : Subgroup (C ⧸ K)) :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h64 h5
    have hle : Nat.card (S₀ ⊔ Subgroup.zpowers h : Subgroup (C ⧸ K)) ≤ 320 :=
      hLcard ▸ Subgroup.card_le_card_group _
    rw [hLcard]
    exact le_antisymm hle (Nat.le_of_dvd Nat.card_pos h320)
  · rw [eq_bot_iff]
    rintro x ⟨hxS, hxh⟩
    rw [Subgroup.mem_bot]
    obtain ⟨k, hk⟩ := hS₀p ⟨x, hxS⟩
    have h1 : orderOf x ∣ 2 ^ k := by
      apply orderOf_dvd_of_pow_eq_one
      have := congrArg Subtype.val hk
      simpa using this
    have h2 : orderOf x ∣ 5 := hhord ▸ orderOf_dvd_of_mem_zpowers hxh
    have hcop : Nat.Coprime 5 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
    exact orderOf_eq_one_iff.mp
      (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h2 hcop) h1)
  · intro x hx
    rw [hcenter] at hx
    rw [Subgroup.mem_center_iff.mp (hEc hx) h, mul_inv_cancel_right]
  · intro x hx hxfix
    rw [hcenter] at hxfix ⊢
    have h1 : πE (h * x * h⁻¹ * x⁻¹) = 1 := by
      rw [hπEdef, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hxfix
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hπEh] at h1
    have hxP : πE x ∈ (Pbar : Subgroup Q) := by
      rw [hPbar_eq]
      exact ⟨x, hx, rfl⟩
    have h2 : hb * πE x * hb⁻¹ = πE x := by
      calc hb * πE x * hb⁻¹ = (hb * πE x * hb⁻¹ * (πE x)⁻¹) * πE x := by group
        _ = πE x := by rw [h1, one_mul]
    have h3 := hfpfb (πE x) hxP h2
    rw [hπEdef, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3
    exact h3
  · rw [hcenter]
    exact ⟨_, Subgroup.mem_subgroupOf.mpr hzZ, rfl⟩
  · intro h1
    rw [hπKdef, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have := hSK1 _ h1 (hZS z hzZ)
    exact hz1 (congrArg Subtype.val this)

end CFSG.LyonsUnitaryFour
