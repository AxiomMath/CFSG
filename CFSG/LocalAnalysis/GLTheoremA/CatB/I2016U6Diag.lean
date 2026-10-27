module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I2016U6Red
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I2016U6TPart
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I2016U6Fix
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I2016U6Y
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I2016U6Lift

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.I2016U6

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Fischer CFSG.LocalAnalysis.GLTheoremA.LevelLieU6
  CFSG.LocalAnalysis.GLTheoremA.CatB.U4InnU6 CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LieType.BorelTits CFSG.LocalAnalysis.GLTheoremA.CatB.U52Layer
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)
open scoped commutatorElement

theorem primeFormUnitary_le_isoU : primeFormUnitary hF4 (idGram F4 6) ≤ isoU := by
  intro A hA
  have h := mem_primeFormUnitary.1 hA
  rw [hF4_bar] at h
  refine (unitaryForm_preserves_iff hF4card (A : Matrix (Fin 6) (Fin 6) F4)).2 ?_
  have hmap : (A : Matrix (Fin 6) (Fin 6) F4).map (unitaryInvolution F4 2 1) =
      (A : Matrix (Fin 6) (Fin 6) F4).map bar := by
    ext i j
    simp only [Matrix.map_apply, unitaryInvolution_apply, bar_apply, pow_one]
  rw [hmap]
  simpa [Matrix.mul_one] using h

theorem d_ne_zero {D : GL (Fin 6) F4} {d : Fin 6 → F4}
    (hD : (D : Matrix (Fin 6) (Fin 6) F4) = Matrix.diagonal d) (i : Fin 6) : d i ≠ 0 := by
  intro h0
  have h1 := congrFun (congrFun (D.val_inv) i) i
  rw [hD, Matrix.diagonal_mul, h0, zero_mul, Matrix.one_apply_eq] at h1
  exact zero_ne_one h1

theorem u6KeyDiag {D : GL (Fin 6) F4} {d : Fin 6 → F4}
    (hD : (D : Matrix (Fin 6) (Fin 6) F4) = Matrix.diagonal d)
    (hDu : D ∈ primeFormUnitary hF4 (idGram F4 6)) (hnc : ¬ ∀ i, d i = d 0)
    (π : M6 →* S6) (hπs : Function.Surjective π)
    (hπk : ∀ z ∈ π.ker, ∃ c : F4ˣ,
      (z : GL (Fin 6) F4) = Matrix.GeneralLinearGroup.scalar (Fin 6) c)
    (β : MulAut S6) (hαβ : ∀ u : M6, π (conjM6 ⟨D, hDu⟩ u) = β (π u))
    (H P T : Subgroup S6) (hHβ : ∀ x ∈ H, β x = x) (hA6 : I2016.HasA6Quot H)
    (hPβ : ∀ x ∈ P, β x = x)
    (hPq : ∃ (Tq : Type) (_ : Group Tq) (f : ↥P →* Tq), Function.Surjective f ∧ IsSimpleGroup Tq ∧
        Nat.card Tq = 25920 ∧ Nat.Coprime 3 (Nat.card f.ker))
    (hT0 : T ≠ ⊥) (hT2 : IsPGroup 2 ↥T) (hTβ : T.map β.toMonoidHom = T)
    (hHT : H ≤ Subgroup.normalizer (T : Set S6)) :
    ∃ R : Subgroup S6, R ≠ ⊥ ∧ IsPGroup 2 ↥R ∧ P ≤ Subgroup.normalizer (R : Set S6) ∧
      R.map β.toMonoidHom = R := by
  classical
  have hd0 : ∀ i, d i ≠ 0 := d_ne_zero hD
  set α : MulAut M6 := conjM6 ⟨D, hDu⟩ with hα
  have hCenFix : u4Fix α = CenD D := u4Fix_conjM6 ⟨D, hDu⟩
  have hαD : ∀ x : M6, ((α x : M6) : GL (Fin 6) F4) = D * (x : GL (Fin 6) F4) * D⁻¹ :=
    fun x => rfl
  have hZc : π.ker ≤ Subgroup.center M6 := by
    intro z hz
    obtain ⟨c, hc⟩ := hπk z hz
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    change (g : GL (Fin 6) F4) * z = z * g
    rw [hc]
    exact (commute_scalar c (g : GL (Fin 6) F4)).eq
  have hZ3 : ∀ z ∈ π.ker, z ^ 3 = 1 := by
    intro z hz
    obtain ⟨c, hc⟩ := hπk z hz
    apply Subtype.ext
    show (z : GL (Fin 6) F4) ^ 3 = 1
    rw [hc, ← map_pow, F4unit_pow_three, map_one]
  have hZα : ∀ z ∈ π.ker, α z = z := by
    intro z hz
    obtain ⟨c, hc⟩ := hπk z hz
    apply Subtype.ext
    rw [hαD, hc, (commute_scalar c D).eq, mul_inv_cancel_right]
  obtain ⟨Tq, _, f, hf, hTs, hTc, hker⟩ := hPq
  haveI : IsSimpleGroup Tq := hTs
  haveI : Finite Tq := Nat.finite_of_card_ne_zero (by rw [hTc]; norm_num)
  haveI : Group.IsPerfect Tq := CatB.I1431YD4.isPerfect_of_simple (by rw [hTc]; norm_num)
  haveI : Finite S6 := Finite.of_surjective π hπs
  obtain ⟨LP, hLPperf, hLPfix, hLPP, hLPs⟩ := exists_perfect_lift hπs hZc hαβ P hPβ f hf
  have hLPC : LP ≤ CenD D := by rw [← hCenFix]; exact hLPfix
  have hdvdLP : 25920 ∣ Nat.card LP := by
    let φP : ↥LP →* Tq := f.comp ((π.comp LP.subtype).codRestrict P (fun x => hLPP x.1 x.2))
    have hφP : Function.Surjective φP := by
      intro t
      obtain ⟨x, hx, h, hxf⟩ := hLPs t
      exact ⟨⟨x, hx⟩, hxf⟩
    have := Subgroup.card_dvd_of_surjective hφP
    rwa [hTc] at this
  obtain ⟨A₀, S₆, hS₆g, fA, hA₀H, hSc, hfA⟩ := hA6
  obtain ⟨hSsimp, hS360⟩ := CatB.I1431YU5.isA6_isSimpleGroup hSc
  haveI : IsSimpleGroup S₆ := hSsimp
  haveI : Group.IsPerfect S₆ := CatB.I1431YD4.isPerfect_of_simple (by rw [hS360]; norm_num)
  obtain ⟨LA, hLAperf, hLAfix, hLAP, hLAs⟩ :=
    exists_perfect_lift hπs hZc hαβ A₀ (fun x hx => hHβ x (hA₀H hx)) fA hfA
  have hLAC : LA ≤ CenD D := by rw [← hCenFix]; exact hLAfix
  let φA : ↥LA →* S₆ := fA.comp ((π.comp LA.subtype).codRestrict A₀ (fun x => hLAP x.1 x.2))
  have hφA : Function.Surjective φA := by
    intro t
    obtain ⟨x, hx, h, hxf⟩ := hLAs t
    exact ⟨⟨x, hx⟩, hxf⟩
  have hσ : ∀ x : M6, π (α x) ∈ T ↔ π x ∈ T := by
    intro x
    rw [hαβ x]
    constructor
    · intro h
      rw [← hTβ] at h
      obtain ⟨w, hw, hwz⟩ := Subgroup.mem_map.1 h
      have : w = π x := β.injective hwz
      rw [← this]
      exact hw
    · intro h
      have : β (π x) ∈ T.map β.toMonoidHom := Subgroup.mem_map_of_mem _ h
      rwa [hTβ] at this
  have hX : ∀ x ∈ LA, ∀ y ∈ T, π x * y * (π x)⁻¹ ∈ T := fun x hx y hy =>
    (Subgroup.mem_normalizer_iff.1 (hHT (hA₀H (hLAP x hx))) y).1 hy
  obtain ⟨T', hT'0, hT'2, hT'N, hT'α⟩ :=
    exists_lift_two_subgroup π hπs (fun x hx => hZc hx) hT0 hT2 hX α hσ
  have hDT : ∀ t ∈ T', ∃ t' ∈ T', (t' : GL (Fin 6) F4) = D * (t : GL (Fin 6) F4) * D⁻¹ := by
    intro t ht
    refine ⟨α t, ?_, rfl⟩
    have : α t ∈ T'.map α.toMonoidHom := Subgroup.mem_map_of_mem _ ht
    rwa [hT'α] at this
  have hDT' : ∀ t ∈ T', ∃ t' ∈ T', (t' : GL (Fin 6) F4) = D⁻¹ * (t : GL (Fin 6) F4) * D := by
    intro t ht
    have : t ∈ T'.map α.toMonoidHom := by rw [hT'α]; exact ht
    obtain ⟨s, hs, hst⟩ := Subgroup.mem_map.1 this
    refine ⟨s, hs, ?_⟩
    have h1 : D * (s : GL (Fin 6) F4) * D⁻¹ = (t : GL (Fin 6) F4) := congrArg Subtype.val hst
    rw [← h1]
    group
  have hbig : ∃ c : F4, 4 ≤ Fintype.card (Blk d c) := by
    by_contra hno
    push Not at hno
    have hbot := eq_bot_of_perfect_of_small hD (fun c => by have := hno c; omega) hLPC hLPperf
    rw [hbot, Subgroup.card_bot] at hdvdLP
    exact absurd (Nat.le_of_dvd one_pos hdvdLP) (by norm_num)
  obtain ⟨c, hc4⟩ := hbig
  have hc5 := card_blk_le_five d hnc c
  have hsmall2 : ∀ c' : F4, c' ≠ c → Fintype.card (Blk d c') ≤ 2 := fun c' hc' => by
    have := card_blk_add_le d (c := c) (c' := c') (Ne.symm hc')
    omega
  have hsmall3 : ∀ c' : F4, c' ≠ c → Fintype.card (Blk d c') ≤ 3 := fun c' hc' =>
    (hsmall2 c' hc').trans (by norm_num)
  by_cases h2 : ∃ c₂ : F4, c₂ ≠ c ∧ Fintype.card (Blk d c₂) = 2
  ·
    obtain ⟨c₂, hne2, hcard2⟩ := h2
    have hne : c ≠ c₂ := Ne.symm hne2
    have hsum := card_blk_add_le d hne
    have h6 : Fintype.card (Blk d c) + Fintype.card (Blk d c₂) = 6 := by omega
    have hcover := cover_of_card (d := d) c c₂ hne h6
    have hY6 : Nat.card (Rc hD c) = 6 := card_Rc hD c c₂ hne hcover hcard2
    have hPCfix : P.comap π ≤ u4Fix α :=
      preimage_le_fix hZc hZ3 hZα hαβ P hPβ f hker LP hLPfix hLPP hLPs
    have hPCC : P.comap π ≤ CenD D := by rw [← hCenFix]; exact hPCfix
    have hLmP : LP.map π ≤ P := by
      rintro _ ⟨x, hx, rfl⟩
      exact hLPP x hx
    have hNG : (LP.map π).comap π ≤ P.comap π := fun n hn => hLmP hn
    have hNY : ∀ n ∈ (LP.map π).comap π, ∀ y ∈ Rc hD c, n * y = y * n := by
      intro n hn y hy
      obtain ⟨l, hl, hln⟩ := hn
      have hz : l⁻¹ * n ∈ π.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hln, inv_mul_cancel]
      have hzc := Subgroup.mem_center_iff.1 (hZc hz) y
      have hn' : n = l * (l⁻¹ * n) := by group
      have hcomm := comm_Rc_of_perfect hD c hsmall3 hLPC hLPperf l hl y hy
      calc n * y = (l * (l⁻¹ * n)) * y := by rw [← hn']
        _ = l * ((l⁻¹ * n) * y) := mul_assoc _ _ _
        _ = l * (y * (l⁻¹ * n)) := by rw [← hzc]
        _ = (l * y) * (l⁻¹ * n) := (mul_assoc _ _ _).symm
        _ = (y * l) * (l⁻¹ * n) := by rw [hcomm]
        _ = y * (l * (l⁻¹ * n)) := mul_assoc _ _ _
        _ = y * n := by rw [← hn']
    have hGY : ∀ g ∈ P.comap π, ∀ y ∈ Rc hD c, g * y * g⁻¹ ∈ Rc hD c :=
      fun g hg y hy => Rc_normal_CenD hD c (hPCC hg) hy
    have hidx := relIndex_coprime hπs P f hf hker LP hLPP hLPs
    obtain ⟨t, htY, ht1, ht2, htfix⟩ :=
      exists_fixed_involution (Rc hD c) hY6 (P.comap π) hGY ((LP.map π).comap π) hNG hNY hidx
    obtain ⟨-, htC, -⟩ := (mem_Rc hD c).1 htY
    have htα : α t = t := by
      have : t ∈ u4Fix α := by rw [hCenFix]; exact htC
      exact this
    have hord : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact ht2) ht1
    have hαs : ∀ s ∈ Subgroup.zpowers t, α s = s := by
      intro s hs
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hs
      rw [map_zpow, htα]
    refine ⟨(Subgroup.zpowers t).map π, ?_, ?_, ?_, ?_⟩
    · intro hbot
      have hmem : π t ∈ (Subgroup.zpowers t).map π :=
        Subgroup.mem_map_of_mem π (Subgroup.mem_zpowers t)
      rw [hbot, Subgroup.mem_bot] at hmem
      have htk : t ∈ π.ker := hmem
      have h3 := hZ3 t htk
      apply ht1
      calc t = t * (t * t) := by rw [ht2, mul_one]
        _ = t ^ 3 := (pow_three t).symm
        _ = 1 := h3
    · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have h2g : IsPGroup 2 ↥(Subgroup.zpowers t) :=
        IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord]; norm_num)
      exact h2g.map π
    · have hRc : ∀ q ∈ P, ∀ r ∈ (Subgroup.zpowers t).map π, q * r = r * q := by
        intro q hq r hr
        obtain ⟨y, hy, rfl⟩ := hr
        obtain ⟨x, rfl⟩ := hπs q
        have hxPC : x ∈ P.comap π := hq
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
        have h1 : x * t * x⁻¹ = t := htfix x hxPC
        have h2' : x * t = t * x := by
          calc x * t = (x * t * x⁻¹) * x := by group
            _ = t * x := by rw [h1]
        have hct : Commute x t := h2'
        have h3 : x * t ^ k = t ^ k * x := (hct.zpow_right k).eq
        rw [← map_mul, ← map_mul, h3]
      intro p hp
      rw [Subgroup.mem_normalizer_iff]
      intro r
      constructor
      · intro hr
        rw [hRc p hp r hr, mul_inv_cancel_right]
        exact hr
      · intro hr
        have h1 := hRc p⁻¹ (P.inv_mem hp) _ hr
        have e : r = p⁻¹ * (p * r * p⁻¹) * p := by group
        rw [e, h1, inv_mul_cancel_right]
        exact hr
    · ext y
      constructor
      · rintro ⟨r, ⟨s, hs, rfl⟩, rfl⟩
        have : β (π s) = π s := by
          have := hαβ s
          rw [hαs s hs] at this
          exact this.symm
        show β (π s) ∈ _
        rw [this]
        exact Subgroup.mem_map_of_mem π hs
      · rintro ⟨s, hs, rfl⟩
        refine ⟨π s, Subgroup.mem_map_of_mem π hs, ?_⟩
        have := hαβ s
        rw [hαs s hs] at this
        exact this.symm
  ·
    exfalso
    push Not at h2
    have hsing : ∀ i, d i ≠ c → Fintype.card (Blk d (d i)) ≤ 1 := by
      intro i hi
      have h2' := hsmall2 (d i) hi
      have h2'' := h2 (d i) hi
      omega
    exact no_T_small hD (primeFormUnitary_le_isoU hDu) hd0 c hc4 hc5 hsing LA hLAC hLAperf hS360
      φA hφA T' hT'0 hT'2 hT'N hDT hDT'

end CFSG.LocalAnalysis.GLTheoremA.CatB.I2016U6

end
