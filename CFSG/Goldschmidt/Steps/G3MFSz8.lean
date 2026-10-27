module

import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiCentralCover
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.BenderSuzukiBorel
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderBasic

public section

namespace CFSG.Goldschmidt

open CFSG.Open

namespace MFSz8

open CFSG.ComponentClassification.AschbacherToolkit.Bender

section Triple

variable {K : Type*} [Group K]

theorem mul_sq_eq {a a' : K} (hc : a' * a * a'⁻¹ * a⁻¹ ∈ Subgroup.center K) :
    (a * a') ^ 2 = a' * a * a'⁻¹ * a⁻¹ * (a ^ 2 * a' ^ 2) := by
  obtain ⟨c, hcd⟩ : ∃ c, c = a' * a * a'⁻¹ * a⁻¹ := ⟨_, rfl⟩
  rw [← hcd] at hc ⊢
  have h1 : a' * a = c * a * a' := by rw [hcd]; group
  have h2 : a * c = c * a := Subgroup.mem_center_iff.mp hc a
  calc (a * a') ^ 2 = a * (a' * a) * a' := by rw [sq]; group
    _ = a * c * (a * a' * a') := by rw [h1]; group
    _ = c * a * (a * a' * a') := by rw [h2]
    _ = c * (a ^ 2 * a' ^ 2) := by simp only [sq]; group

theorem commutator_mul_right_eq {u v w : K} (hc : u * w * u⁻¹ * w⁻¹ ∈ Subgroup.center K) :
    u * (v * w) * u⁻¹ * (v * w)⁻¹ = u * w * u⁻¹ * w⁻¹ * (u * v * u⁻¹ * v⁻¹) := by
  obtain ⟨c, hcd⟩ : ∃ c, c = u * w * u⁻¹ * w⁻¹ := ⟨_, rfl⟩
  rw [← hcd] at hc ⊢
  have h : u * v * u⁻¹ * c = c * (u * v * u⁻¹) := Subgroup.mem_center_iff.mp hc _
  calc u * (v * w) * u⁻¹ * (v * w)⁻¹ = u * v * u⁻¹ * c * v⁻¹ := by rw [hcd]; group
    _ = c * (u * v * u⁻¹) * v⁻¹ := by rw [h]
    _ = c * (u * v * u⁻¹ * v⁻¹) := by group

theorem sq_eq_one_of_transitive {N A : Subgroup K} (hN : N ≤ Subgroup.center K)
    (hN2 : ∀ n ∈ N, n ^ 2 = 1) (hsq : ∀ a ∈ A, a ^ 2 ∈ N)
    (hcomm : ∀ a ∈ A, ∀ a' ∈ A, a * a' * a⁻¹ * a'⁻¹ ∈ N)
    (htrans : ∀ a ∈ A, ∀ a' ∈ A, a ∉ N → a' ∉ N → ∃ g : K, g⁻¹ * a * g * a'⁻¹ ∈ N)
    {u v w : K} (hu : u ∈ A) (hv : v ∈ A) (hw : w ∈ A) (hu1 : u ∉ N) (hv1 : v ∉ N)
    (hw1 : w ∉ N) (hvu : v * u ∉ N) (hwu : w * u ∉ N) (hvw : v * w ∉ N)
    (hvwu : v * w * u ∉ N) {a : K} (ha : a ∈ A) : a ^ 2 = 1 := by
  have hconst : ∀ x ∈ A, x ∉ N → x ^ 2 = u ^ 2 := by
    intro x hx hxN
    obtain ⟨g, hg⟩ := htrans u hu x hx hu1 hxN
    obtain ⟨n, hnd⟩ : ∃ n, n = g⁻¹ * u * g * x⁻¹ := ⟨_, rfl⟩
    rw [← hnd] at hg
    have hn2 := hN2 n hg
    have hxn : x * n = n * x := Subgroup.mem_center_iff.mp (hN hg) x
    have hgu : g * u ^ 2 = u ^ 2 * g := Subgroup.mem_center_iff.mp (hN (hsq u hu)) g
    have hux : g⁻¹ * u * g = n * x := by rw [hnd]; group
    calc x ^ 2 = n ^ 2 * x ^ 2 := by rw [hn2, one_mul]
      _ = n * (n * x) * x := by simp only [sq]; group
      _ = n * (x * n) * x := by rw [← hxn]
      _ = (g⁻¹ * u * g) ^ 2 := by rw [hux]; simp only [sq]; group
      _ = g⁻¹ * (u ^ 2 * g) := by simp only [sq]; group
      _ = g⁻¹ * (g * u ^ 2) := by rw [← hgu]
      _ = u ^ 2 := by group
  have hc : ∀ x ∈ A, ∀ y ∈ A, x ∉ N → y ∉ N → x * y ∉ N →
      y * x * y⁻¹ * x⁻¹ = (u ^ 2)⁻¹ := by
    intro x hx y hy hxN hyN hxyN
    have key := mul_sq_eq (hN (hcomm y hy x hx))
    rw [hconst _ (A.mul_mem hx hy) hxyN, hconst x hx hxN, hconst y hy hyN] at key
    rw [eq_mul_inv_of_mul_eq key.symm]
    group
  have h1 := hc v hv u hu hv1 hu1 hvu
  have h2 := hc w hw u hu hw1 hu1 hwu
  have h3 := hc (v * w) (A.mul_mem hv hw) u hu hvw hu1 hvwu
  rw [commutator_mul_right_eq (hN (hcomm u hu w hw)), h1, h2] at h3
  have hu2 : u ^ 2 = 1 := inv_eq_one.mp (mul_eq_right.mp h3)
  by_cases haN : a ∈ N
  · exact hN2 a haN
  · rw [hconst a ha haN, hu2]

theorem exists_independent {S : Subgroup K} [Finite S] (hS2 : ∀ z ∈ S, z ^ 2 = 1)
    (hcard : 4 < Nat.card S) :
    ∃ u ∈ S, ∃ v ∈ S, ∃ w ∈ S, u ≠ 1 ∧ v ≠ 1 ∧ w ≠ 1 ∧ v * u ≠ 1 ∧ w * u ≠ 1 ∧
      v * w ≠ 1 ∧ v * w * u ≠ 1 := by
  classical
  have hout : ∀ F : Finset K, F.card < Nat.card S → ∃ x ∈ S, x ∉ F := by
    intro F hF
    by_contra h
    push Not at h
    have hinj : Function.Injective (fun x : S => (⟨x, h x x.2⟩ : F)) := fun x y hxy =>
      Subtype.ext (congrArg (fun p : F => (p : K)) hxy)
    have hle := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_eq_finsetCard] at hle
    omega
  have hinv : ∀ z ∈ S, z⁻¹ = z := fun z hz =>
    inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hS2 z hz)
  obtain ⟨u, hu, hu'⟩ := hout {1} (by rw [Finset.card_singleton]; omega)
  obtain ⟨v, hv, hv'⟩ := hout {1, u} (lt_of_le_of_lt Finset.card_le_two (by omega))
  obtain ⟨w, hw, hw'⟩ := hout {1, u, v, v * u} (lt_of_le_of_lt Finset.card_le_four (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hu' hv' hw'
  obtain ⟨hv1, hvu⟩ := hv'
  obtain ⟨hw1, hwu, hwv, hwvu⟩ := hw'
  refine ⟨u, hu, v, hv, w, hw, hu', hv1, hw1, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · exact hvu ((eq_inv_of_mul_eq_one_left h).trans (hinv u hu))
  · exact hwu ((eq_inv_of_mul_eq_one_left h).trans (hinv u hu))
  · exact hwv ((eq_inv_of_mul_eq_one_right h).trans (hinv v hv))
  · apply hwvu
    calc w = v⁻¹ * (v * w * u) * u⁻¹ := by group
      _ = v⁻¹ * u⁻¹ := by rw [h]; group
      _ = v * u := by rw [hinv v hv, hinv u hu]

end Triple

theorem comm_and_sq_of_benderBorel {X : Type*} [Group X] [Finite X] {q k : ℕ}
    (hB : fusionBenderBorel X q k) (hq : 4 < q) {K : Type*} [Group K] [Finite K]
    (π : K →* X) (hπ : Function.Surjective π) (hker : π.ker = Subgroup.center K)
    (hZ2 : ∀ z ∈ Subgroup.center K, z ^ 2 = 1) (T : Sylow 2 K) {b c : K}
    (hbT : b ∈ (T : Subgroup K)) (hcT : c ∈ (T : Subgroup K))
    (hb : ∀ x ∈ (T : Subgroup K), b * x * b⁻¹ * x⁻¹ ∈ Subgroup.center K)
    (hc : ∀ x ∈ (T : Subgroup K), c * x * c⁻¹ * x⁻¹ ∈ Subgroup.center K) :
    b * c = c * b ∧ b ^ 2 = 1 := by
  have hmem : ∀ x, x ∈ Subgroup.center K ↔ π x = 1 := fun x => by
    rw [← hker, MonoidHom.mem_ker]
  let Q : Sylow 2 X := T.mapSurjective hπ
  obtain ⟨hSE, hZQ2, hZQcard, -⟩ := benderBorel_sylowCenter hB Q
  let A : Subgroup K := (sylowCenter (Q : Subgroup X)).comap π
  have hA : ∀ y, y ∈ A ↔ π y ∈ sylowCenter (Q : Subgroup X) := fun y => Iff.rfl
  have hAT : ∀ y ∈ (T : Subgroup K),
      (∀ x ∈ (T : Subgroup K), y * x * y⁻¹ * x⁻¹ ∈ Subgroup.center K) → y ∈ A := by
    intro y hyT hy
    rw [hA, mem_sylowCenter]
    refine ⟨Subgroup.mem_map_of_mem π hyT, fun t ht => ?_⟩
    have ht' : t ∈ (T : Subgroup K).map π := ht
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ht'
    have h := (hmem _).mp (hy x hx)
    simp only [map_mul, map_inv] at h
    calc π x * π y = (π y * π x * (π y)⁻¹ * (π x)⁻¹)⁻¹ * (π y * π x) := by group
      _ = π y * π x := by rw [h, inv_one, one_mul]
  have hsqA : ∀ a ∈ A, a ^ 2 = 1 := by
    obtain ⟨u', hu', v', hv', w', hw', h1, h2, h3, h4, h5, h6, h7⟩ :=
      exists_independent (S := sylowCenter (Q : Subgroup X)) hZQ2 (by rw [hZQcard]; exact hq)
    obtain ⟨u, rfl⟩ := hπ u'
    obtain ⟨v, rfl⟩ := hπ v'
    obtain ⟨w, rfl⟩ := hπ w'
    have hnot : ∀ y, π y ≠ 1 → y ∉ Subgroup.center K := fun y hy h => hy ((hmem y).mp h)
    have hsq : ∀ a ∈ A, a ^ 2 ∈ Subgroup.center K := by
      intro a ha
      rw [hmem, map_pow]
      exact hZQ2 (π a) ((hA a).mp ha)
    have hcomm : ∀ a ∈ A, ∀ a' ∈ A, a * a' * a⁻¹ * a'⁻¹ ∈ Subgroup.center K := by
      intro a ha a' ha'
      have hc' : π a' * π a = π a * π a' :=
        (mem_sylowCenter.mp ((hA a).mp ha)).2 (π a') (sylowCenter_le _ ((hA a').mp ha'))
      rw [hmem]
      simp only [map_mul, map_inv]
      rw [← hc']
      group
    have htrans : ∀ a ∈ A, ∀ a' ∈ A, a ∉ Subgroup.center K → a' ∉ Subgroup.center K →
        ∃ g : K, g⁻¹ * a * g * a'⁻¹ ∈ Subgroup.center K := by
      intro a ha a' ha' haN ha'N
      have ha1 : π a ≠ 1 := fun h => haN ((hmem a).mpr h)
      have ha'1 : π a' ≠ 1 := fun h => ha'N ((hmem a').mpr h)
      obtain ⟨n, -, hn⟩ :=
        normalizer_transitive_center hSE hZQ2 ((hA a).mp ha) ((hA a').mp ha') ha1 ha'1
      obtain ⟨g, rfl⟩ := hπ n
      refine ⟨g, ?_⟩
      rw [hmem]
      simp only [map_mul, map_inv]
      rw [hn, mul_inv_cancel]
    intro a ha
    exact sq_eq_one_of_transitive le_rfl hZ2 hsq hcomm htrans hu' hv' hw' (hnot _ h1)
      (hnot _ h2) (hnot _ h3) (hnot _ (by rwa [map_mul])) (hnot _ (by rwa [map_mul]))
      (hnot _ (by rwa [map_mul])) (hnot _ (by rwa [map_mul, map_mul])) ha
  have hbA := hAT b hbT hb
  have hcA := hAT c hcT hc
  have hb2 := hsqA b hbA
  refine ⟨?_, hb2⟩
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hb2)
  have hcinv : c⁻¹ = c := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hsqA c hcA)
  have hbcinv : (b * c)⁻¹ = b * c :=
    inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hsqA (b * c) (A.mul_mem hbA hcA))
  calc b * c = (b * c)⁻¹ := hbcinv.symm
    _ = c⁻¹ * b⁻¹ := mul_inv_rev b c
    _ = c * b := by rw [hbinv, hcinv]

theorem exists_commutator_eq {K : Type} [Group K] [Finite K] [Group.IsPerfect K] {a : ℕ}
    (ha : 1 ≤ a) (π : K →* Sz a) (hπ : Function.Surjective π)
    (hker : π.ker = Subgroup.center K) (hZ2 : ∀ z ∈ Subgroup.center K, z ^ 2 = 1)
    (T : Sylow 2 K) {b : K}
    (hb : ∀ x ∈ (T : Subgroup K), b * x * b⁻¹ * x⁻¹ ∈ Subgroup.center K)
    (hbZ : b ∉ Subgroup.center K) {z : K} (hz : z ∈ Subgroup.center K) :
    ∃ x ∈ (T : Subgroup K), x * b * x⁻¹ * b⁻¹ = z := by
  have hmem : ∀ x, x ∈ Subgroup.center K ↔ π x = 1 := fun x => by
    rw [← hker, MonoidHom.mem_ker]
  have hcent : ∀ x ∈ (T : Subgroup K), x * b * x⁻¹ * b⁻¹ ∈ Subgroup.center K := by
    intro x hx
    have h := (Subgroup.center K).inv_mem (hb x hx)
    have heq : (b * x * b⁻¹ * x⁻¹)⁻¹ = x * b * x⁻¹ * b⁻¹ := by group
    rwa [heq] at h
  let φ : (T : Subgroup K) →* K :=
    { toFun := fun x => (x : K) * b * (x : K)⁻¹ * b⁻¹
      map_one' := by simp
      map_mul' := fun x y => by
        obtain ⟨c, hcd⟩ : ∃ c, c = (y : K) * b * (y : K)⁻¹ * b⁻¹ := ⟨_, rfl⟩
        have hcZ : c ∈ Subgroup.center K := by rw [hcd]; exact hcent y y.2
        have h1 : (x : K) * c = c * x := Subgroup.mem_center_iff.mp hcZ x
        have h2 : (x : K) * b * (x : K)⁻¹ * b⁻¹ * c = c * ((x : K) * b * (x : K)⁻¹ * b⁻¹) :=
          Subgroup.mem_center_iff.mp hcZ _
        simp only [Subgroup.coe_mul]
        rw [← hcd, h2]
        calc (x : K) * y * b * ((x : K) * y)⁻¹ * b⁻¹
            = (x : K) * c * (b * (x : K)⁻¹ * b⁻¹) := by rw [hcd]; group
          _ = c * (x : K) * (b * (x : K)⁻¹ * b⁻¹) := by rw [h1]
          _ = c * ((x : K) * b * (x : K)⁻¹ * b⁻¹) := by group }
  by_contra hne
  push Not at hne
  let Z₀ : Subgroup K := φ.range
  have hZ₀ : Z₀ ≤ Subgroup.center K := by
    rintro _ ⟨x, rfl⟩
    exact hcent x x.2
  have hzZ₀ : z ∉ Z₀ := by
    rintro ⟨x, hx⟩
    exact hne x x.2 hx
  have : Z₀.Normal := Subgroup.normal_of_le_center hZ₀
  let η : K ⧸ Z₀ →* Sz a := QuotientGroup.lift Z₀ π (by rw [hker]; exact hZ₀)
  have hηmk : ∀ x : K, η x = π x := fun x => QuotientGroup.lift_mk _ _ x
  have hη : Function.Surjective η := by
    intro y
    obtain ⟨x, rfl⟩ := hπ y
    exact ⟨x, hηmk x⟩
  have hηker : ∀ x : K, (x : K ⧸ Z₀) ∈ η.ker ↔ x ∈ Subgroup.center K := fun x => by
    rw [MonoidHom.mem_ker, hηmk, hmem]
  have hkc : η.ker ≤ Subgroup.center (K ⧸ Z₀) := by
    intro q hq
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    have hx := (hηker x).mp hq
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.mp hx y]
  have hkp : IsPGroup 2 η.ker := by
    intro q
    refine ⟨1, Subtype.ext ?_⟩
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (q : K ⧸ Z₀)
    have hxZ : x ∈ Subgroup.center K := (hηker x).mp (by rw [hx]; exact q.2)
    simp only [pow_one, Subgroup.coe_pow, OneMemClass.coe_one]
    rw [← hx, ← QuotientGroup.mk_pow, hZ2 x hxZ, QuotientGroup.mk_one]
  have hkne : η.ker ≠ ⊥ := by
    intro hbot
    have hzk := (hηker z).mpr hz
    rw [hbot, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hzk
    exact hzZ₀ hzk
  obtain ⟨hcentP, -⟩ := CFSG.ShultStronglyClosedTI.suzukiCover_native_nontrivial_Sylow_centralizer
    a ha η hη hkc hkp hkne
  let P : Sylow 2 (K ⧸ Z₀) := T.mapSurjective (QuotientGroup.mk'_surjective Z₀)
  have hbP : (b : K ⧸ Z₀) ∈ Subgroup.centralizer ((P : Subgroup (K ⧸ Z₀)) : Set (K ⧸ Z₀)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : y ∈ (T : Subgroup K).map (QuotientGroup.mk' Z₀) := hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy'
    have h1 : ((x * b * x⁻¹ * b⁻¹ : K) : K ⧸ Z₀) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr ⟨⟨x, hx⟩, rfl⟩
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h1
    rw [QuotientGroup.mk'_apply]
    calc (x : K ⧸ Z₀) * (b : K ⧸ Z₀) = (x : K ⧸ Z₀) * (b : K ⧸ Z₀) * (x : K ⧸ Z₀)⁻¹ *
        (b : K ⧸ Z₀)⁻¹ * ((b : K ⧸ Z₀) * (x : K ⧸ Z₀)) := by group
      _ = (b : K ⧸ Z₀) * (x : K ⧸ Z₀) := by rw [h1, one_mul]
  have hbk : (b : K ⧸ Z₀) ∈ η.ker := by
    rw [← hcentP P]
    exact hbP
  exact hbZ ((hηker b).mp hbk)

end MFSz8

theorem GMFSz8 :
    ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
      IsElemAbelian 2 (Subgroup.center K) → Nonempty (K ⧸ Subgroup.center K ≃* Sz 1) →
      ∀ T : Sylow 2 K,
      (∀ b ∈ (T : Subgroup K), ∀ c ∈ (T : Subgroup K),
        (∀ x ∈ (T : Subgroup K), b * x * b⁻¹ * x⁻¹ ∈ Subgroup.center K) →
        (∀ x ∈ (T : Subgroup K), c * x * c⁻¹ * x⁻¹ ∈ Subgroup.center K) →
        b * c = c * b ∧ b ^ 2 = 1) ∧
      ∀ b ∈ (T : Subgroup K), (∀ x ∈ (T : Subgroup K), b * x * b⁻¹ * x⁻¹ ∈ Subgroup.center K) →
        b ∉ Subgroup.center K → ∀ z ∈ Subgroup.center K, ∃ x ∈ (T : Subgroup K),
          x * b * x⁻¹ * b⁻¹ = z := by
  intro K _ _ hK hZ ⟨e⟩ T
  have : Group.IsPerfect K := ⟨hK.1⟩
  let π : K →* Sz 1 := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = Subgroup.center K :=
    (MonoidHom.ker_comp_of_injective _ e.toMonoidHom e.injective).trans
      (QuotientGroup.ker_mk' _)
  have : Finite (Sz 1) := Finite.of_surjective π hπ
  refine ⟨fun b hbT c hcT hb hc => ?_, fun b _ hb hbZ z hz => ?_⟩
  · exact MFSz8.comm_and_sq_of_benderBorel (bender_suzuki_borel_full 1 le_rfl) (by norm_num)
      π hπ hker hZ.2 T hbT hcT hb hc
  · exact MFSz8.exists_commutator_eq le_rfl π hπ hker hZ.2 T hb hbZ hz

end CFSG.Goldschmidt
