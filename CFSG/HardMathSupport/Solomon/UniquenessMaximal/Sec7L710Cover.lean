module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710YBasic
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710Tools
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710CoverA
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710CoverB

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {B T I : Subgroup G}

theorem eq_one_of_piQ_eq_one (B T I : Subgroup G) (x : ↥(wOf B T I))
    (hx : ∃ n : ℕ, x ^ (2 ^ n) = 1) (h : piQ B T I x = 1) : x = 1 := by
  obtain ⟨n, hn⟩ := hx
  have hxZ : x ∈ (zOf B T I).subgroupOf (wOf B T I) := (QuotientGroup.eq_one_iff x).1 h
  let y : ↥(zOf B T I) := ⟨x, hxZ⟩
  have hy : y ^ (2 ^ n) = 1 := Subtype.ext (by simpa [y] using congrArg Subtype.val hn)
  have h1 : orderOf y ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hy
  have h2 : orderOf y ∣ Nat.card ↥(zOf B T I) := orderOf_dvd_natCard y
  have hcop : Nat.Coprime (2 ^ n) (Nat.card ↥(zOf B T I)) :=
    Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2
      (not_two_dvd_card_zOf B T I))
  have h3 : orderOf y = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
  have : y = 1 := orderOf_eq_one_iff.1 h3
  exact Subtype.ext (by simpa [y] using congrArg Subtype.val this)

theorem piQ_injOn_tSub (h : Setup710 B T I) :
    ∀ x ∈ T.subgroupOf (wOf B T I), piQ B T I x = 1 → x = 1 := by
  intro x hx hx1
  refine eq_one_of_piQ_eq_one B T I x ?_ hx1
  obtain ⟨k, hk⟩ := h.tTwo (⟨x, hx⟩ : ↥T)
  exact ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk)⟩

theorem tripleOf_tX (h : Setup710 B T I) (i : Fin 3) :
    tripleOf (tX B T I) i =
      (tripleOf (T.subgroupOf (wOf B T I)) i).map (piQ B T I) :=
  tripleOf_map (piQ_injOn_tSub h) i

theorem map_subtype_tripleOf_subgroupOf (h : Setup710 B T I) (i : Fin 3) :
    (tripleOf (T.subgroupOf (wOf B T I)) i).map (wOf B T I).subtype = tripleOf T i := by
  have hT : T ≤ wOf B T I := t_le_wOf h
  have := tripleOf_map (f := (wOf B T I).subtype) (T₁ := T.subgroupOf (wOf B T I))
    (fun x _ hx => Subtype.ext (by simpa using hx)) i
  rw [Subgroup.map_subgroupOf_eq_of_le hT] at this
  exact this.symm

omit [Finite G] in
theorem coe_mem_normalizer_map {W : Subgroup G} {K : Subgroup W} {n : W}
    (hn : n ∈ Subgroup.normalizer (K : Set W)) :
    (n : G) ∈ Subgroup.normalizer ((K.map W.subtype : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨n * k * n⁻¹, (Subgroup.mem_normalizer_iff.1 hn k).1 hk, rfl⟩
  · rintro ⟨k', hk', hk'x⟩
    refine ⟨n⁻¹ * k' * n, ?_, ?_⟩
    · have h3 : n * (n⁻¹ * k' * n) * n⁻¹ ∈ K := by
        have : n * (n⁻¹ * k' * n) * n⁻¹ = k' := by group
        rw [this]; exact hk'
      exact (Subgroup.mem_normalizer_iff.1 hn (n⁻¹ * k' * n)).2 h3
    · have h1 : ((k' : W) : G) = (n : G) * x * (n : G)⁻¹ := hk'x
      calc (((n⁻¹ * k' * n : W)) : G) = (n : G)⁻¹ * ((k' : W) : G) * (n : G) := by simp
        _ = x := by rw [h1]; group

theorem preQ_normalizer_decomp (h : Setup710 B T I) (i : Fin 3) {g : G}
    (hg : g ∈ preQ B T I
      (Subgroup.normalizer (tripleOf (tX B T I) i : Set (XQ B T I)))) :
    ∃ z ∈ zOf B T I, ∃ n ∈ Subgroup.normalizer (tripleOf T i : Set G) ⊓ wOf B T I,
      g = z * n := by
  obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hg
  set U₁ : Subgroup ↥(wOf B T I) := tripleOf (T.subgroupOf (wOf B T I)) i with hU₁
  set Z₁ : Subgroup ↥(wOf B T I) := (zOf B T I).subgroupOf (wOf B T I) with hZ₁
  have hw' : piQ B T I w ∈ Subgroup.normalizer ((U₁.map (piQ B T I) : Subgroup (XQ B T I)) :
      Set (XQ B T I)) := by
    have := Subgroup.mem_comap.1 hw
    rwa [tripleOf_tX h i] at this
  have hker : (U₁.map (piQ B T I)).comap (piQ B T I) = U₁ ⊔ Z₁ := by
    rw [Subgroup.comap_map_eq, show (piQ B T I).ker = Z₁ from QuotientGroup.ker_mk' _]
  have hwM : w ∈ Subgroup.normalizer ((U₁ ⊔ Z₁ : Subgroup ↥(wOf B T I)) : Set ↥(wOf B T I)) := by
    rw [← hker, ← Subgroup.comap_normalizer_eq_of_surjective _
      (QuotientGroup.mk'_surjective Z₁)]
    exact hw'
  have hZcard : ¬ 2 ∣ Nat.card Z₁ := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (zOf_le_wOf B T I)).toEquiv]
    exact not_two_dvd_card_zOf B T I
  have hU₁2 : IsPGroup 2 U₁ :=
    (Sec7.tripleOf_isPGroup (h.tTwo.comap_subtype (K := wOf B T I)) i :)
  obtain ⟨z, hz, n, hn, hzn⟩ := frattini_odd_normal hZcard hU₁2 hwM
  refine ⟨z, hz, n, ⟨?_, n.2⟩, by rw [hzn]; rfl⟩
  rw [← map_subtype_tripleOf_subgroupOf h i]
  exact coe_mem_normalizer_map hn

theorem cover_of_subset {B T I : Subgroup G} (h : Setup710 B T I) (hf : YFacts B T I) (i : Fin 3)
    (hsub : (I : Set G) ⊆
      (preQ B T I (Subgroup.normalizer (tripleOf (tX B T I) i : Set (XQ B T I))) : Set G) *
        (pOf B T I : Set G)) :
    I ≤ (Subgroup.normalizer (tripleOf T i : Set G) ⊓ I) ⊔ GLAPPrimeCoreOf 3 I := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N₀ : Subgroup G := Subgroup.normalizer (tripleOf T i : Set G) ⊓ wOf B T I with hN₀
  set P : Subgroup G := pOf B T I with hP
  set Y : Subgroup G := yOf B T I with hY
  have hN₀Y : N₀ ≤ Y := inf_le_right.trans inf_le_right
  have hPY : P ≤ Y := pOf_le_yOf B T I
  have hYP : Y ≤ Subgroup.normalizer (P : Set G) := y_le_normalizer_pOf B T I
  have hYI : Y ≤ Subgroup.normalizer (I : Set G) := y_le_normalizer_I h
  have hZP : zOf B T I ≤ P := zOf_le_pOf hf
  have hN₀P : ∀ x ∈ I, x ∈ N₀ ⊔ P := by
    intro x hx
    obtain ⟨g, hg, p, hp, rfl⟩ := Set.mem_mul.1 (hsub hx)
    obtain ⟨z, hz, n, hn, hgzn⟩ := preQ_normalizer_decomp h i hg
    have hnW : n ∈ wOf B T I := hn.2
    have hz' : n⁻¹ * z * n ∈ zOf B T I := by
      have := (Subgroup.mem_normalizer_iff.1
        (wOf_le_normalizer_zOf B T I (inv_mem hnW)) z).1 hz
      simpa using this
    have : z * n * p = n * ((n⁻¹ * z * n) * p) := by group
    rw [hgzn, this]
    exact Subgroup.mul_mem_sup hn (mul_mem (hZP hz') hp)
  have hgen : ∀ x ∈ I, (∃ n : ℕ, x ^ (3 ^ n) = 1) →
      x ∈ (Subgroup.normalizer (tripleOf T i : Set G) ⊓ I) ⊔ GLAPPrimeCoreOf 3 I := by
    intro x hx ⟨m, hxm⟩
    obtain ⟨z, hz, r, hr, ⟨k, hrk⟩, hxr⟩ :=
      sylow_lift (p := 3) (M := N₀ ⊔ P) (Z := P) (N₀ := N₀) le_sup_left le_sup_right
        (sup_le (hN₀Y.trans hYP) (Subgroup.le_normalizer))
        (not_three_dvd_card_pOf B T I) (by rw [sup_comm]) (hN₀P x hx) hxm
    have hzY : z⁻¹ ∈ Y := Y.inv_mem (hPY hz)
    have hrI : r ∈ I := by
      have h1 := (Subgroup.mem_normalizer_iff.1 (hYI hzY) x).1 hx
      have h2 : r = z⁻¹ * x * z⁻¹⁻¹ := by rw [hxr]; group
      rw [h2]; exact h1
    have hrY : r⁻¹ ∈ Y := Y.inv_mem (hN₀Y hr)
    have hc : r⁻¹ * x ∈ GLAPPrimeCoreOf 3 I := by
      rw [← inf_pOf_eq h]
      refine ⟨I.mul_mem (I.inv_mem hrI) hx, ?_⟩
      have h1 : r⁻¹ * z * r⁻¹⁻¹ ∈ P := by
        have := (Subgroup.mem_normalizer_iff.1 (hYP hrY) z).1 hz
        exact this
      have h2 : r⁻¹ * x = (r⁻¹ * z * r⁻¹⁻¹) * z⁻¹ := by rw [hxr]; group
      rw [h2]
      exact P.mul_mem h1 (P.inv_mem hz)
    have hxrc : x = r * (r⁻¹ * x) := by group
    rw [hxrc]
    exact mul_mem (Subgroup.mem_sup_left ⟨hr.1, hrI⟩) (Subgroup.mem_sup_right hc)
  exact h.gen3.symm.le.trans ((Subgroup.closure_le _).2 fun x hx => hgen x hx.1 hx.2)

end CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710
