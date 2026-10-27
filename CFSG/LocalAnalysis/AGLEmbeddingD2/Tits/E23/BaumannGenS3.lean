module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.E23.BaumannGenAbs
public import CFSG.CGT.PushingUpLit.Transport

public section

namespace CFSG.AGLEmbeddingD2.Tits.E23

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.G6 CFSG.Open CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS5

@[expose] def threeCycle : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2

theorem threeCycle_pow_three : threeCycle ^ 3 = 1 := by decide +kernel

theorem threeCycle_ne_one : threeCycle ≠ 1 := by decide +kernel

set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 2048 in
theorem perm_three_cases : ∀ τ σ : Equiv.Perm (Fin 3), τ * τ = 1 → τ ≠ 1 →
    σ = 1 ∨ σ = τ ∨ σ = threeCycle * τ * threeCycle⁻¹ ∨
      σ = τ * (threeCycle * τ * threeCycle⁻¹) ∨ σ = (threeCycle * τ * threeCycle⁻¹) * τ ∨
      σ = τ * (threeCycle * τ * threeCycle⁻¹) * τ := by
  decide +kernel

theorem permAct_threeCycle_fix : ∀ x : PermMod 3, (∑ i, Multiplicative.toAdd x i = 0) →
    permAct 3 threeCycle x = x → x = 1 := by
  decide +kernel

theorem permMod_split : ∀ τ : Equiv.Perm (Fin 3), τ * τ = 1 → τ ≠ 1 →
    ∀ x : PermMod 3, (∑ i, Multiplicative.toAdd x i = 0) →
      ∃ a b : PermMod 3, (∑ i, Multiplicative.toAdd a i = 0) ∧ (∑ i, Multiplicative.toAdd b i = 0) ∧
        permAct 3 τ a = a ∧ permAct 3 (threeCycle * τ * threeCycle⁻¹) b = b ∧ a * b = x := by
  decide +kernel

section Sym3

variable {V : Type} [CommGroup V] {E : Subgroup (MulAut V)}

theorem sym3_fix_iff (θ : ↥E ≃* Equiv.Perm (Fin 3)) (β : ↥(commV E) →* coreMod 3)
    (hinv : ∀ x ∈ E, ∀ p ∈ commV E, x p ∈ commV E) (hinj : Function.Injective β)
    (hequiv : ∀ (x : ↥E) (p : ↥(commV E)) (hp : (x : MulAut V) p ∈ commV E),
      β ⟨(x : MulAut V) p, hp⟩ = coreAct 3 (θ x) (β p))
    (u : ↥E) (p : ↥(commV E)) :
    (u : MulAut V) (p : V) = p ↔ coreAct 3 (θ u) (β p) = β p := by
  have hm := hinv u u.2 p p.2
  have h := hequiv u p hm
  constructor
  · intro hf
    rw [← h]
    exact congrArg β (Subtype.ext hf)
  · intro h2
    rw [← h] at h2
    exact congrArg Subtype.val (hinj h2)

theorem exists_goodEl_of_symThree (θ : ↥E ≃* Equiv.Perm (Fin 3)) (β : ↥(commV E) →* coreMod 3)
    (hinv : ∀ x ∈ E, ∀ p ∈ commV E, x p ∈ commV E) (hsurj : Function.Surjective β)
    (hker : β.ker = ⊥)
    (hequiv : ∀ (x : ↥E) (p : ↥(commV E)) (hp : (x : MulAut V) p ∈ commV E),
      β ⟨(x : MulAut V) p, hp⟩ = coreAct 3 (θ x) (β p))
    {R : Subgroup (MulAut V)} (hRE : R ≤ E) (hR2 : Nat.card R = 2) : ∃ y, GoodEl E R y := by
  classical
  have hinj : Function.Injective β := (MonoidHom.ker_eq_bot_iff β).1 hker
  let βe : ↥(commV E) ≃* coreMod 3 := MulEquiv.ofBijective β ⟨hinj, hsurj⟩
  have key : ∀ a b : ↥R, a ≠ b → (∀ s : ↥R, s = a ∨ s = b) →
      ∃ r : ↥R, r ≠ 1 ∧ ∀ s : ↥R, s = 1 ∨ s = r := by
    intro a b hab hmem
    rcases hmem 1 with h1 | h1
    · refine ⟨b, fun hb => hab (h1.symm.trans hb.symm), fun s => ?_⟩
      rcases hmem s with h | h
      · exact Or.inl (h.trans h1.symm)
      · exact Or.inr h
    · refine ⟨a, fun ha => hab (ha.trans h1), fun s => ?_⟩
      rcases hmem s with h | h
      · exact Or.inr h
      · exact Or.inl (h.trans h1.symm)
  obtain ⟨r, hr1, hRset⟩ : ∃ r : ↥R, r ≠ 1 ∧ ∀ s : ↥R, s = 1 ∨ s = r := by
    obtain ⟨a, b, hab, huniv⟩ := Nat.card_eq_two_iff.1 hR2
    refine key a b hab fun s => ?_
    have h : s ∈ ({a, b} : Set ↥R) := by
      rw [huniv]
      exact Set.mem_univ s
    simpa using h
  have hRset' : ∀ s ∈ R, s = 1 ∨ s = (r : MulAut V) := by
    intro s hs
    rcases hRset ⟨s, hs⟩ with h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h)
  have hrr : (r : MulAut V) * r = 1 := by
    rcases hRset (r * r) with h | h
    · simpa using congrArg Subtype.val h
    · exact absurd (by simpa using h) hr1
  let r' : ↥E := ⟨(r : MulAut V), hRE r.2⟩
  have hr'1 : r' ≠ 1 := fun h =>
    hr1 (Subtype.ext (show (r : MulAut V) = 1 from congrArg Subtype.val h))
  have hr'r' : r' * r' = 1 := Subtype.ext hrr
  have hτ1 : θ r' ≠ 1 := fun h => hr'1 (θ.injective (h.trans (map_one θ).symm))
  have hτ2 : θ r' * θ r' = 1 := by rw [← map_mul, hr'r', map_one]
  let y : ↥E := θ.symm threeCycle
  have hθy : θ y = threeCycle := θ.apply_symm_apply _
  let r'' : ↥E := y * r' * y⁻¹
  have hθr'' : θ r'' = threeCycle * θ r' * threeCycle⁻¹ := by
    simp only [r'', map_mul, map_inv, hθy]
  have hy3 : y ^ 3 = 1 := θ.injective (by rw [map_pow, hθy, threeCycle_pow_three, map_one])
  have hy1 : y ≠ 1 := fun h => threeCycle_ne_one (by rw [← hθy, h, map_one])
  have hy3' : (y : MulAut V) ^ 3 = 1 := by simpa using congrArg Subtype.val hy3
  have hy1' : (y : MulAut V) ≠ 1 := fun h => hy1 (Subtype.ext h)
  have hr''mem : (r'' : MulAut V) ∈ conjSub (y : MulAut V) R := by
    have := mem_conjSub_of_mem (g := (y : MulAut V)) r.2
    simpa [r''] using this
  have hRy : ∀ s ∈ conjSub (y : MulAut V) R, s = 1 ∨ s = (r'' : MulAut V) := by
    intro s hs
    rw [mem_conjSub_iff] at hs
    rcases hRset' _ hs with h | h
    · left
      have : s = (y : MulAut V) * ((y : MulAut V)⁻¹ * s * y) * (y : MulAut V)⁻¹ := by group
      rw [this, h]
      group
    · right
      have : s = (y : MulAut V) * ((y : MulAut V)⁻¹ * s * y) * (y : MulAut V)⁻¹ := by group
      rw [this, h]
      rfl
  refine ⟨(y : MulAut V), y.2, ?_, ?_, ?_, ?_⟩
  · exact orderOf_eq_prime hy3' hy1'
  ·
    intro e he
    have hr_mem : (r' : MulAut V) ∈ R ⊔ conjSub (y : MulAut V) R := Subgroup.mem_sup_left r.2
    have hr''_mem : (r'' : MulAut V) ∈ R ⊔ conjSub (y : MulAut V) R :=
      Subgroup.mem_sup_right hr''mem
    have hcase := perm_three_cases (θ r') (θ ⟨e, he⟩) hτ2 hτ1
    rw [← hθr''] at hcase
    rcases hcase with h | h | h | h | h | h
    · have : (⟨e, he⟩ : ↥E) = 1 := θ.injective (h.trans (map_one θ).symm)
      have he1 : e = 1 := congrArg Subtype.val this
      rw [he1]; exact one_mem _
    · have : (⟨e, he⟩ : ↥E) = r' := θ.injective h
      rw [show e = (r' : MulAut V) from congrArg Subtype.val this]; exact hr_mem
    · have : (⟨e, he⟩ : ↥E) = r'' := θ.injective h
      rw [show e = (r'' : MulAut V) from congrArg Subtype.val this]; exact hr''_mem
    · have : (⟨e, he⟩ : ↥E) = r' * r'' := θ.injective (h.trans (map_mul θ r' r'').symm)
      rw [show e = (r' : MulAut V) * r'' from congrArg Subtype.val this]
      exact mul_mem hr_mem hr''_mem
    · have : (⟨e, he⟩ : ↥E) = r'' * r' := θ.injective (h.trans (map_mul θ r'' r').symm)
      rw [show e = (r'' : MulAut V) * r' from congrArg Subtype.val this]
      exact mul_mem hr''_mem hr_mem
    · have : (⟨e, he⟩ : ↥E) = r' * r'' * r' := by
        refine θ.injective (h.trans ?_)
        rw [map_mul θ (r' * r'') r', map_mul θ r' r'']
      rw [show e = (r' : MulAut V) * r'' * r' from congrArg Subtype.val this]
      exact mul_mem (mul_mem hr_mem hr''_mem) hr_mem
  ·
    intro w hw hyw
    have hfix := (sym3_fix_iff θ β hinv hinj hequiv y ⟨w, hw⟩).1 hyw
    rw [hθy] at hfix
    have hone : β ⟨w, hw⟩ = 1 := by
      have := permAct_threeCycle_fix (β ⟨w, hw⟩ : PermMod 3) (β ⟨w, hw⟩).2
        (congrArg Subtype.val hfix)
      exact Subtype.ext this
    have hw1 : (⟨w, hw⟩ : ↥(commV E)) = 1 := by
      rw [← MonoidHom.mem_ker, hker] at hone
      exact hone
    have : w = 1 := congrArg Subtype.val hw1
    rw [this]
    exact one_mem _
  ·
    intro w hw
    obtain ⟨a₀, b₀, ha₀, hb₀, hτa, hτb, hab⟩ := permMod_split (θ r') hτ2 hτ1
      (β ⟨w, hw⟩ : PermMod 3) (β ⟨w, hw⟩).2
    let ua : ↥(coreMod 3) := ⟨a₀, mem_coreMod.2 ha₀⟩
    let ub : ↥(coreMod 3) := ⟨b₀, mem_coreMod.2 hb₀⟩
    let pa : ↥(commV E) := βe.symm ua
    let pb : ↥(commV E) := βe.symm ub
    have hpa : β pa = ua := βe.apply_symm_apply ua
    have hpb : β pb = ub := βe.apply_symm_apply ub
    refine ⟨(pa : V), ⟨pa.2, fun s hs => ?_⟩, (pb : V), ⟨pb.2, fun s hs => ?_⟩, ?_⟩
    · rcases hRset' s hs with h | h
      · rw [h]; rfl
      · rw [h]
        refine (sym3_fix_iff θ β hinv hinj hequiv r' pa).2 ?_
        rw [hpa]
        exact Subtype.ext hτa
    · rcases hRy s hs with h | h
      · rw [h]; rfl
      · rw [h]
        refine (sym3_fix_iff θ β hinv hinj hequiv r'' pb).2 ?_
        rw [hpb, hθr'']
        exact Subtype.ext hτb
    · have h1 : β (pa * pb) = β ⟨w, hw⟩ := by
        rw [map_mul, hpa, hpb]
        exact Subtype.ext hab
      have h2 : pa * pb = ⟨w, hw⟩ := hinj h1
      exact (congrArg Subtype.val h2).symm

variable [Finite V]

theorem exists_goodEl_of_symType {M : Subgroup (MulAut V)} {D : Set (Subgroup (MulAut V))}
    (hSym : SymType M D E) (hcard : Nat.card E = 6) {R : Subgroup (MulAut V)}
    (hR : IsSylowOf 2 R E) : ∃ y, GoodEl E R y := by
  obtain ⟨m, θ, β, -, h3, hinv, hsurj, hker, hequiv, -, -, -⟩ := hSym
  have hm3 : m = 3 := by
    have h1 : Nat.card E = m.factorial := by
      rw [Nat.card_congr θ.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm,
        Fintype.card_fin]
    rw [hcard] at h1
    by_contra hne
    have h4 : 4 ≤ m := by omega
    have := Nat.factorial_dvd_factorial h4
    rw [← h1] at this
    norm_num [Nat.factorial] at this
  subst hm3
  have hR2 : Nat.card R = 2 := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hR.2.1
    have h1 := Subgroup.relIndex_mul_card R E
    rw [inf_eq_left.2 hR.1, hk, hcard] at h1
    have hk3 : k < 3 := by
      by_contra hk3
      have : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hpos : 0 < R.relIndex E := Nat.pos_of_ne_zero (fun h0 => by rw [h0] at h1; omega)
      nlinarith
    have hodd := hR.2.2
    interval_cases k
    · exfalso
      apply hodd
      simp at h1
      omega
    · simpa using hk
    · exfalso
      omega
  exact exists_goodEl_of_symThree θ β hinv hsurj hker hequiv hR.1 hR2

end Sym3

end CFSG.AGLEmbeddingD2.Tits.E23
