module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk41RConj
public import CFSG.LieType.BorelTits.CentralQuotient

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk41R

open Subgroup Matrix CFSG.GH74.GLS.IVK.Proofs2
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped commutatorElement

section Quot

variable {S : Type} [Group S]

theorem eq_one_of_pow_eq_one_of_coprime {p : ℕ} (Z : Subgroup S) (hZ : Nat.Coprime (Nat.card Z) p)
    {w : S} (hwZ : w ∈ Z) {k : ℕ} (hk : w ^ p ^ k = 1) : w = 1 := by
  have hZc : w ^ Nat.card Z = 1 := congrArg Subtype.val (pow_card_eq_one' (x := (⟨w, hwZ⟩ : Z)))
  have := pow_gcd_eq_one.mpr ⟨hZc, hk⟩
  rwa [(hZ.pow_right k).gcd_eq_one, pow_one] at this

theorem eq_one_of_isPGroup_mem {p : ℕ} (Z V : Subgroup S) (hZ : Nat.Coprime (Nat.card Z) p)
    (hV : IsPGroup p V) {w : S} (hwV : w ∈ V) (hwZ : w ∈ Z) : w = 1 := by
  obtain ⟨k, hk⟩ := hV ⟨w, hwV⟩
  exact eq_one_of_pow_eq_one_of_coprime Z hZ hwZ (k := k) (by simpa using congrArg Subtype.val hk)

theorem card_map_of_injOn {H : Type} [Group H] (f : S →* H) (V : Subgroup S)
    (hinj : ∀ x ∈ V, ∀ y ∈ V, f x = f y → x = y) : Nat.card (V.map f) = Nat.card V := by
  symm
  refine Nat.card_eq_of_bijective
    (fun v : V => (⟨f v, Subgroup.mem_map_of_mem f v.2⟩ : V.map f)) ⟨?_, ?_⟩
  · intro a b hab
    exact Subtype.ext (hinj a a.2 b b.2 (congrArg Subtype.val hab))
  · rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩

theorem mk_injOn_of_isPGroup {p : ℕ} (Z : Subgroup S) [Z.Normal] (hZ : Nat.Coprime (Nat.card Z) p)
    (V : Subgroup S) (hV : IsPGroup p V) :
    ∀ x ∈ V, ∀ y ∈ V, QuotientGroup.mk' Z x = QuotientGroup.mk' Z y → x = y := by
  intro x hx y hy hxy
  have hmem : x⁻¹ * y ∈ Z := QuotientGroup.eq.mp hxy
  have := eq_one_of_isPGroup_mem Z V hZ hV (V.mul_mem (V.inv_mem hx) hy) hmem
  rw [inv_mul_eq_one] at this
  exact this

theorem commute_of_mk_commute {p : ℕ} (Z : Subgroup S) [Z.Normal] (hZc : Z ≤ center S)
    (hZ : Nat.Coprime (Nat.card Z) p) {x s : S} {k : ℕ} (hx : x ^ p ^ k = 1)
    (h : QuotientGroup.mk' Z x * QuotientGroup.mk' Z s =
      QuotientGroup.mk' Z s * QuotientGroup.mk' Z x) :
    x * s = s * x := by
  have hc : s * x * s⁻¹ * x⁻¹ ∈ Z := by
    rw [← QuotientGroup.ker_mk' Z, MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
    exact h.symm
  have hcen : Commute (s * x * s⁻¹ * x⁻¹) x := (Subgroup.mem_center_iff.mp (hZc hc) x).symm
  have hconj : s * x * s⁻¹ = (s * x * s⁻¹ * x⁻¹) * x := by group
  have hpow : (s * x * s⁻¹ * x⁻¹) ^ p ^ k = 1 := by
    have h1 : (s * x * s⁻¹) ^ p ^ k = 1 := by
      rw [conj_pow, hx, mul_one, mul_inv_cancel]
    rw [hconj, hcen.mul_pow, hx, mul_one] at h1
    exact h1
  have h1 := eq_one_of_pow_eq_one_of_coprime Z hZ hc hpow
  rw [h1, one_mul] at hconj
  have : s * x = x * s := by
    calc s * x = s * x * s⁻¹ * s := by group
      _ = x * s := by rw [hconj]
  exact this.symm

theorem rgood_quotient [Finite S] {p n : ℕ} [Fact p.Prime] (Z : Subgroup S) [Z.Normal]
    (hZc : Z ≤ center S) (hZ : Nat.Coprime (Nat.card Z) p) (h3 : ∀ w ∈ Z, w ^ 3 = 1)
    (hS : ∀ (a : S) (X : Subgroup S), orderOf a = 2 → X ≤ centralizer ({a} : Set S) →
      Nat.card X = p ^ n → RGood p n a X)
    {z : S ⧸ Z} (hz : orderOf z = 2) {X : Subgroup (S ⧸ Z)}
    (hXz : X ≤ centralizer ({z} : Set (S ⧸ Z))) (hXp : IsPGroup p X) (hXc : Nat.card X = p ^ n) :
    RGood p n z X := by
  have hρs : Function.Surjective (QuotientGroup.mk' Z) := QuotientGroup.mk'_surjective Z
  have hker : (QuotientGroup.mk' Z).ker = Z := QuotientGroup.ker_mk' Z
  have hker3 : ∀ w ∈ (QuotientGroup.mk' Z).ker, w ^ 3 = 1 := fun w hw => h3 w (hker ▸ hw)
  have hkerc : (QuotientGroup.mk' Z).ker ≤ center S := by rw [hker]; exact hZc
  have hzz : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz, sq] at this
  obtain ⟨a, haa, hρa⟩ := linConj_lift_involution (QuotientGroup.mk' Z) hρs hker3 hzz
  have ha1 : a ≠ 1 := by
    rintro rfl
    rw [map_one] at hρa
    rw [← hρa, orderOf_one] at hz
    omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ha2 : orderOf a = 2 := orderOf_eq_prime (by rw [sq]; exact haa) ha1
  obtain ⟨V, hVp, hVX⟩ := CFSG.LieType.BorelTits.exists_isPGroup_map_eq Z hXp
  subst hVX
  have hVinj := mk_injOn_of_isPGroup Z hZ V hVp
  have hVc : Nat.card V = p ^ n := by
    rw [← card_map_of_injOn _ V hVinj]
    exact hXc
  have hVC : V ≤ centralizer ({a} : Set S) := by
    intro x hx
    rw [mem_centralizer_singleton_iff]
    have hxz := mem_centralizer_singleton_iff.mp (hXz (Subgroup.mem_map_of_mem _ hx))
    rw [← hρa] at hxz
    exact Lemma41aL3.commute_of_map_commute (QuotientGroup.mk' Z) hkerc hker3 haa hxz
  obtain ⟨R, hR, hRp, hVR, hRC, hRcard, hZ', hVc', hcomm, hza⟩ := hS a V ha2 hVC hVc
  have hCcomap : (centralizer (((V.map (QuotientGroup.mk' Z) : Subgroup (S ⧸ Z))) :
      Set (S ⧸ Z))).comap (QuotientGroup.mk' Z) = centralizer (V : Set S) := by
    ext s
    simp only [mem_comap, mem_centralizer_iff, SetLike.mem_coe]
    constructor
    · intro hs x hx
      have := hs (QuotientGroup.mk' Z x) (Subgroup.mem_map_of_mem _ hx)
      obtain ⟨k, hk⟩ := hVp ⟨x, hx⟩
      exact commute_of_mk_commute Z hZc hZ (k := k) (by simpa using congrArg Subtype.val hk) this
    · intro hs y hy
      obtain ⟨x, hx, rfl⟩ := hy
      rw [← map_mul, ← map_mul, hs x hx]
  have hCmap : centralizer (((V.map (QuotientGroup.mk' Z) : Subgroup (S ⧸ Z))) : Set (S ⧸ Z)) =
      (centralizer (V : Set S)).map (QuotientGroup.mk' Z) := by
    rw [← hCcomap, Subgroup.map_comap_eq_self_of_surjective hρs]
  refine ⟨R.map (QuotientGroup.mk' Z), ?_, hRp.map _, Subgroup.map_mono hVR, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply le_antisymm
    · rw [hCmap, hR]
      exact CFSG.LieType.BorelTits.map_pCoreOf_le (QuotientGroup.mk' Z) _
    · have := CFSG.LieType.BorelTits.pCoreOf_le_map_pCoreOf_comap Z hZc hZ
        (centralizer (((V.map (QuotientGroup.mk' Z) : Subgroup (S ⧸ Z))) : Set (S ⧸ Z)))
      rw [hCcomap, ← hR] at this
      exact this
  · rw [hCmap]
    exact Subgroup.map_mono hRC
  · rw [card_map_of_injOn _ R (mk_injOn_of_isPGroup Z hZ R hRp), hRcard]
  · rintro _ ⟨r, hr, rfl⟩ hc
    have hcomm' : ∀ s ∈ R, r * s = s * r := by
      intro s hs
      have h1 := hc (QuotientGroup.mk' Z s) ⟨s, hs, rfl⟩
      have hd : ⁅r, s⁆ ∈ V := hcomm r hr s hs
      have hdZ : ⁅r, s⁆ ∈ Z := by
        rw [← hker, MonoidHom.mem_ker, map_commutatorElement]
        exact commutatorElement_eq_one_iff_mul_comm.mpr h1
      exact commutatorElement_eq_one_iff_mul_comm.mp
        (eq_one_of_isPGroup_mem Z V hZ hVp hd hdZ)
    exact ⟨r, hZ' r hr hcomm', rfl⟩
  · rw [← Subgroup.map_commutator]
    exact Subgroup.map_mono hVc'
  · rintro _ ⟨r, hr, rfl⟩ _ ⟨s, hs, rfl⟩
    exact ⟨_, hcomm r hr s hs, map_commutatorElement _ r s⟩
  · rintro _ ⟨r, hr, rfl⟩
    refine ⟨a * r * a⁻¹ * r, hza r hr, ?_⟩
    rw [map_mul, map_mul, map_mul, map_inv, hρa]

end Quot

section Proj

variable {F : Type} [Field F]

theorem scalars_pow_three {w : SpecialLinearGroup (Fin 3) F} (hw : w ∈ scalars 3 F) : w ^ 3 = 1 := by
  obtain ⟨c, hc, hwc⟩ := mem_scalars.mp hw
  have hc3 : c * c * c = 1 := by
    rw [← pow_three']
    exact hc
  have h2 : w ^ 3 = w * w * w := pow_three' w
  have hc3' : (c : F) * c * c = 1 := by
    have := congrArg (fun u : Fˣ => (u : F)) hc3
    simpa using this
  rw [h2]
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hwc, Matrix.mul_apply, hc3', Matrix.scalar_apply, Matrix.diagonal_apply]

theorem rgood_projectiveSL3 [Finite F] {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) [CharP F p]
    (hF : Nat.card F = p ^ n) {z : projectiveSL 3 F} (hz : orderOf z = 2)
    {X : Subgroup (projectiveSL 3 F)} (hXz : X ≤ centralizer ({z} : Set (projectiveSL 3 F)))
    (hXp : IsPGroup p X) (hXc : Nat.card X = p ^ n) : RGood p n z X := by
  have : Fact p.Prime := ⟨hp⟩
  exact rgood_quotient (S := SpecialLinearGroup (Fin 3) F) (scalars 3 F) (scalars_le_center 3 F)
    (Lemma41dL3.scalars_coprime hp) (fun w hw => scalars_pow_three hw)
    (fun a X ha hXa hXc => rgood_sl3 hp hp2 hF ha hXa hXc) hz hXz hXp hXc

end Proj

end CFSG.GH74.GLS.IVK.Proofs2.Ivk41R
