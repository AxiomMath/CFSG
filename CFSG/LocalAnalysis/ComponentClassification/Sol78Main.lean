module

public import CFSG.LocalAnalysis.ComponentClassification.Sol78Intrinsic
public import CFSG.LocalAnalysis.ComponentClassification.Sol78Stable
public import CFSG.LocalAnalysis.ComponentClassification.Sol78Swap
public import CFSG.LocalAnalysis.ComponentClassification.Sol78Pump

public section

namespace CFSG.ComponentClassification.Sol78

open CFSG Subgroup UnbalancedLayer UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {X : Type} [Group X] [Finite X]

@[expose] def pairKernel (x : X) (L : Subgroup X) : Subgroup X :=
  centralizer ({x} : Set X) ⊓ coreActionKernel L

@[expose] noncomputable def pairMeasure (x : X) (L : Subgroup X) : ℕ :=
  2 ^ (Nat.card (pairKernel x L)).factorization 2

theorem card_le_pairMeasure {x : X} {L P : Subgroup X} (hP : IsPGroup 2 P)
    (hPD : P ≤ pairKernel x L) : Nat.card P ≤ pairMeasure x L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := (hP.comap_subtype (K := pairKernel x L)).exists_le_sylow
  have h1 : Nat.card (P.comap (pairKernel x L).subtype) = Nat.card P :=
    Nat.card_congr (subgroupOfEquivOfLe hPD).toEquiv
  rw [← h1, pairMeasure, ← Sylow.card_eq_multiplicity S]
  exact Subgroup.card_le_of_le hS

theorem exists_sylow_centralizing (hSchur : SolAltLit.SchurAlternatingMultiplierInput) {x : X}
    {L : Subgroup X} {m : ℕ} (hP : IsDoublePair x L m) :
    ∃ y : X, orderOf y = 2 ∧ y ∈ L ∧
      (∀ l ∈ L, l⁻¹ * y⁻¹ * l * y ∈ (pPrimeCore 2 L).map L.subtype) ∧
      ∃ Q : Subgroup X, IsPGroup 2 Q ∧ Q ≤ centralizer ({x} : Set X) ∧ Q ≤ coreActionKernel L ∧
        Q ≤ centralizer ({y} : Set X) ∧ Nat.card Q = pairMeasure x L := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hZ2, -⟩ := hP.coreQuotient hSchur
  obtain ⟨hx, hLx, hL, -, -, -, -⟩ := hP
  set O := pPrimeCore 2 L with hO
  set π := QuotientGroup.mk' O with hπ
  set Z := Open.fusionZStar L with hZ
  have hZcomap : Z = (center (L ⧸ O)).comap π := fusionZStar_eq_comap L
  have hZcomm : ∀ z ∈ Z, ∀ l : L, l⁻¹ * z⁻¹ * l * z ∈ O := by
    intro z hz l
    rw [hZcomap, mem_comap, mem_center_iff] at hz
    have h1 : π (l⁻¹ * z⁻¹ * l * z) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv]
      have := hz (π l)
      calc (π l)⁻¹ * (π z)⁻¹ * π l * π z = (π l)⁻¹ * (π z)⁻¹ * (π l * π z) := by group
        _ = (π l)⁻¹ * (π z)⁻¹ * (π z * π l) := by rw [this]
        _ = 1 := by group
    rwa [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  have hZcard : Nat.card Z = Nat.card O * 2 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (O.subgroupOf Z)
    have h2 : Nat.card (O.subgroupOf Z) = Nat.card O :=
      Nat.card_congr (subgroupOfEquivOfLe (pPrimeCore_le_fusionZStar L)).toEquiv
    have h3 : Nat.card (Z ⧸ O.subgroupOf Z) = 2 := by
      rw [← hZ2]
      have hmap : Z.map π = center (L ⧸ O) := by
        rw [hZcomap]
        exact map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective O) _
      have hker : (π.comp Z.subtype).ker = O.subgroupOf Z := by
        ext z
        rw [MonoidHom.mem_ker, MonoidHom.comp_apply, mem_subgroupOf, hπ,
          QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        rfl
      have hrange : (π.comp Z.subtype).range = Z.map π := by
        rw [MonoidHom.range_comp, Subgroup.range_subtype]
      rw [← hker, Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv, hrange, hmap]
    rw [h1, h2, h3, mul_comm]
  obtain ⟨y₀, hy₀⟩ := exists_prime_orderOf_dvd_card' (G := Z) 2 (by rw [hZcard]; simp)
  set y : X := ((y₀ : L) : X) with hy
  have hyo : orderOf y = 2 := by rw [hy, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hy₀]
  have hyL : y ∈ L := (y₀ : L).2
  have hyK : ∀ l ∈ L, l⁻¹ * y⁻¹ * l * y ∈ (pPrimeCore 2 L).map L.subtype := by
    intro l hl
    refine ⟨_, hZcomm _ y₀.2 ⟨l, hl⟩, ?_⟩
    simp [hy]
  set ZX : Subgroup X := Z.map L.subtype with hZX
  set D := pairKernel x L with hD
  have hZXD : ZX ≤ D := by
    rintro _ ⟨z, hz, rfl⟩
    refine mem_inf.mpr ⟨hLx z.2, ⟨mem_normalizer_iff.mpr fun w => ?_, fun j hj => ?_⟩⟩
    · constructor
      · intro hw
        exact mul_mem (mul_mem z.2 hw) (inv_mem z.2)
      · intro hw
        have : w = (z : X)⁻¹ * (z * w * (z : X)⁻¹) * z := by group
        rw [this]
        exact mul_mem (mul_mem (inv_mem z.2) hw) z.2
    · exact ⟨_, hZcomm z hz ⟨j, hj⟩, by simp⟩
  have hDZX : ∀ g ∈ D, ∀ w ∈ ZX, g * w * g⁻¹ ∈ ZX := by
    intro g hg w hw
    obtain ⟨z, hz, rfl⟩ := hw
    have hgK : g⁻¹ ∈ coreActionKernel L := inv_mem (mem_inf.mp hg).2
    have h1 := hgK.2 z z.2
    rw [inv_inv] at h1
    obtain ⟨o, ho, hoe⟩ := h1
    have hgz : g * (z : X) * g⁻¹ ∈ L :=
      (mem_normalizer_iff.mp (mem_inf.mp hg).2.1 z).mp z.2
    refine ⟨⟨_, hgz⟩, ?_, rfl⟩
    have hzo : (⟨_, hgz⟩ : L) = z * o := by
      apply Subtype.ext
      show g * (z : X) * g⁻¹ = (z : X) * (o : X)
      have hoe' : (o : X) = (z : X)⁻¹ * g * z * g⁻¹ := hoe
      rw [hoe']
      group
    rw [hzo]
    exact mul_mem hz (pPrimeCore_le_fusionZStar L ho)
  have hyD : y ∈ D := hZXD ⟨y₀, y₀.2, rfl⟩
  have hyP : IsPGroup 2 (zpowers (⟨y, hyD⟩ : D)) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, hyo, pow_one]
  obtain ⟨S, hSy⟩ := hyP.exists_le_sylow
  set Q : Subgroup X := (S : Subgroup D).map D.subtype with hQ
  have hQD : Q ≤ D := map_subtype_le _
  have hyQ : y ∈ Q := ⟨⟨y, hyD⟩, hSy (mem_zpowers _), rfl⟩
  have hQZ : ∀ w ∈ Q, w ∈ ZX → w = 1 ∨ w = y := by
    intro w hwQ hwZ
    by_contra hw
    push Not at hw
    obtain ⟨hw1, hwy⟩ := hw
    set I := Q ⊓ ZX with hI
    have hI2 : IsPGroup 2 I := (S.isPGroup'.map D.subtype).to_inf_left
    have hIL : I ≤ L := inf_le_right.trans (map_subtype_le _)
    let f : I →* L ⧸ O := π.comp (inclusion hIL)
    have hfinj : Function.Injective f := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro i hi
      rw [MonoidHom.mem_ker] at hi
      have hiO : (⟨i, hIL i.2⟩ : L) ∈ O := by
        rw [← QuotientGroup.eq_one_iff]
        exact hi
      obtain ⟨k, hk⟩ := hI2 i
      have h1 : orderOf (⟨i, hIL i.2⟩ : L) ∣ 2 ^ k := by
        apply orderOf_dvd_of_pow_eq_one
        apply Subtype.ext
        have := congrArg (fun z : I => (z : X)) hk
        simpa using this
      have h2 := O.orderOf_dvd_natCard hiO
      have h3 : orderOf (⟨i, hIL i.2⟩ : L) = 1 := Nat.Coprime.eq_one_of_dvd
        (Nat.Coprime.coprime_dvd_left h1 (Nat.Coprime.pow_left k
          (pPrimeCore_coprime_card (p := 2) (G := L)))) h2
      rw [orderOf_eq_one_iff] at h3
      have h4 : ((⟨i, hIL i.2⟩ : L) : X) = 1 := by rw [h3]; rfl
      exact Subtype.ext h4
    have hfZ : ∀ i : I, f i ∈ center (L ⧸ O) := by
      intro i
      have hiZ : ((inclusion hIL i : L)) ∈ Z := by
        obtain ⟨z, hz, hze⟩ := (mem_inf.mp i.2).2
        have : (inclusion hIL i : L) = z := Subtype.ext hze.symm
        rw [this]
        exact hz
      rw [hZcomap, mem_comap] at hiZ
      exact hiZ
    have hcard : Nat.card I ≤ 2 := by
      rw [← hZ2]
      exact Nat.card_le_card_of_injective (fun i => (⟨f i, hfZ i⟩ : center (L ⧸ O)))
        (fun a b h => hfinj (congrArg Subtype.val h))
    have h3 : 3 ≤ Nat.card I := by
      have hyI : y ∈ I := mem_inf.mpr ⟨hyQ, ⟨y₀, y₀.2, rfl⟩⟩
      have hwI : w ∈ I := mem_inf.mpr ⟨hwQ, hwZ⟩
      have hy1 : y ≠ 1 := fun h => by rw [h, orderOf_one] at hyo; norm_num at hyo
      have hsub : ({1, y, w} : Set X) ⊆ (I : Set X) := by
        intro a ha
        rcases ha with rfl | rfl | rfl
        · exact one_mem I
        · exact hyI
        · exact hwI
      have hyw : y ≠ w := fun h => hwy h.symm
      have hc3 : ({1, y, w} : Set X).ncard = 3 := by
        rw [Set.ncard_insert_of_notMem, Set.ncard_pair hyw]
        rintro (h | h)
        · exact hy1 h.symm
        · exact hw1 h.symm
      calc 3 = ({1, y, w} : Set X).ncard := hc3.symm
        _ ≤ (I : Set X).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
        _ = Nat.card I := (Nat.card_coe_set_eq _).symm
    omega
  refine ⟨y, hyo, hyL, hyK, Q, S.isPGroup'.map D.subtype, hQD.trans inf_le_left,
    hQD.trans inf_le_right, ?_, ?_⟩
  · intro q hq
    rw [mem_centralizer_singleton_iff]
    have hqD : q ∈ D := hQD hq
    have hc := hQZ (q * y * q⁻¹) (mul_mem (mul_mem hq hyQ) (inv_mem hq))
      (hDZX q hqD y ⟨y₀, y₀.2, rfl⟩)
    rcases hc with h | h
    · exfalso
      have : y = 1 := by
        calc y = q⁻¹ * (q * y * q⁻¹) * q := by group
          _ = 1 := by rw [h]; group
      rw [this, orderOf_one] at hyo
      norm_num at hyo
    · calc q * y = q * y * q⁻¹ * q := by group
        _ = y * q := by rw [h]
  · rw [hQ, Subgroup.card_map_of_injective D.subtype_injective, Sylow.card_eq_multiplicity S]
    rfl

theorem not_isDoublePair (h2An : GSThmB.Solomon2AnInput) (hCI : GSLit.ClassicalInvolutionInput)
    (hS : SchreierFor Blueprint.Catalog) (hSchur : SolAltLit.SchurAlternatingMultiplierInput)
    (hHe : TBLit.HeldTrivialMultiplier) (hPump : AlternatingPumpUpInput) [IsSimpleGroup X]
    (hnonab : ∃ a b : X, a * b ≠ b * a) (hK : Assembly.KProper Blueprint.Catalog X)
    (hU : ¬ OutcomeLocal.UOutcome X)
    (hspor : ¬ (Nonempty (X ≃* Blueprint.NativeSporadic.M11) ∨
      Nonempty (X ≃* Blueprint.NativeSporadic.McL) ∨
      Nonempty (X ≃* Blueprint.NativeSporadic.Ly))) :
    ∀ (x : X) (L : Subgroup X) (m : ℕ), ¬ IsDoublePair x L m := by
  classical
  intro x₀ L₀ m₀ hP₀
  let S := {p : X × Subgroup X // ∃ m, IsDoublePair p.1 p.2 m}
  have : Nonempty S := ⟨⟨(x₀, L₀), m₀, hP₀⟩⟩
  obtain ⟨⟨⟨x, L⟩, m, hP⟩, hmax⟩ := Finite.exists_max (fun p : S => pairMeasure p.1.1 p.1.2)
  obtain ⟨y, hy, hyL, hyK, Q, hQ, hQx, hQL, hQy, hQcard⟩ := exists_sylow_centralizing hSchur hP
  have hyZ : y ∉ center X := by
    have hZ : center X = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center X) with h | h
      · exact h
      · exfalso
        obtain ⟨a, b, hab⟩ := hnonab
        exact hab ((mem_center_iff.mp (h ▸ mem_top a : a ∈ center X)) b).symm
    rw [hZ, mem_bot]
    intro h
    rw [h, orderOf_one] at hy
    norm_num at hy
  obtain ⟨hTxy, hTpc, -, hcore, ⟨φ, -⟩, hyT, M, hMy, hM, hTM, hTMpc⟩ :=
    pump_setup hS hK hP.1 hy hyZ hP.2.1 hP.2.2.1 hyL hyK
  by_cases hMx : conjugate M x = M
  · obtain ⟨m', hP', hyM⟩ :=
      stable_pump_up hPump hHe hSchur hK hP hy hyZ hTxy hTpc φ hyT hMy hM hTM hMx
    exact hspor (sporadic_of_isDoublePair_of_mem h2An hCI hSchur hnonab hU hP' hyM)
  · obtain ⟨hP', P, hPp, hPK, hPcard⟩ :=
      swap_pump_up hSchur hP hy hTxy hcore φ hyT hMy hM hTM hTMpc hMx hQ hQx hQL hQy
    have h1 : Nat.card P ≤ pairMeasure y M := card_le_pairMeasure hPp hPK
    have h2 : pairMeasure y M ≤ pairMeasure x L := hmax ⟨(y, M), m, hP'⟩
    have h3 : Nat.card Q = pairMeasure x L := hQcard
    omega

end CFSG.ComponentClassification.Sol78
