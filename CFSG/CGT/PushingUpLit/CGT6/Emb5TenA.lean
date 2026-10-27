module

public import CFSG.CGT.PushingUpLit.CGT6.Emb5TenQ
public import CFSG.CGT.PushingUpLit.CGT6.Emb5TenPerm

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUpLit
open Equiv.Perm (viaEmbeddingHom)
open scoped commutatorElement

section Base

variable {V : Type} [CommGroup V] [Finite V] {G T Y L : Subgroup (MulAut V)} {t : MulAut V}

structure TenAlt (L Y : Subgroup (MulAut V)) (N : ℕ) where
  e : LQ L ≃* alternatingGroup (Fin N)
  c : alternatingGroup (Fin N)
  c3 : (c : Equiv.Perm (Fin N)).IsThreeCycle
  hY : (tilde (L := L) Y).map e.toMonoidHom = Subgroup.zpowers c

variable {N : ℕ}

@[expose] def TenAlt.eps (A : TenAlt L Y N) : LQ L →* Equiv.Perm (Fin N) :=
  (alternatingGroup (Fin N)).subtype.comp A.e.toMonoidHom

omit [Finite V] in
theorem TenAlt.eps_injective (A : TenAlt L Y N) : Function.Injective A.eps :=
  Subtype.val_injective.comp A.e.injective

omit [Finite V] in
theorem TenAlt.eps_apply (A : TenAlt L Y N) (x : LQ L) :
    A.eps x = ((A.e x : alternatingGroup (Fin N)) : Equiv.Perm (Fin N)) :=
  rfl

omit [Finite V] in
theorem TenAlt.exists_lift (A : TenAlt L Y N) {σ : Equiv.Perm (Fin N)}
    (hσ : σ ∈ alternatingGroup (Fin N)) : ∃ x : ↥L, A.eps (lpi L x) = σ := by
  obtain ⟨x, hx⟩ := lpi_surjective (L := L) (A.e.symm ⟨σ, hσ⟩)
  refine ⟨x, ?_⟩
  rw [TenAlt.eps_apply, hx]
  simp

omit [Finite V] in
theorem TenAlt.exists_y (A : TenAlt L Y N) :
    ∃ y : ↥L, (y : MulAut V) ∈ Y ∧ A.eps (lpi L y) = (A.c : Equiv.Perm (Fin N)) := by
  have hc : A.c ∈ (tilde (L := L) Y).map A.e.toMonoidHom := by
    rw [A.hY]; exact Subgroup.mem_zpowers _
  obtain ⟨s, hs, hsc⟩ := hc
  obtain ⟨a, ha, haY, rfl⟩ := mem_tilde.mp hs
  refine ⟨⟨a, ha⟩, haY, ?_⟩
  rw [TenAlt.eps_apply]
  exact congrArg Subtype.val hsc

omit [Finite V] in
theorem TenAlt.eps_mem_zpowers (A : TenAlt L Y N) {y : ↥L} (hy : (y : MulAut V) ∈ Y) :
    ∃ m : ℤ, A.eps (lpi L y) = (A.c : Equiv.Perm (Fin N)) ^ m := by
  have h1 : A.e (lpi L y) ∈ Subgroup.zpowers A.c := by
    rw [← A.hY]
    exact ⟨lpi L y, mem_tilde.mpr ⟨y, y.2, hy, rfl⟩, rfl⟩
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp h1
  refine ⟨m, ?_⟩
  rw [TenAlt.eps_apply, ← hm]
  simp

theorem TenCfg.noCentralTwo (hc : TenCfg G T Y t L) : NoCentralTwo L := by
  intro z hz k hk
  apply Subtype.ext
  refine Emb5Layer.central_eq_one_of_two hc.cfg hc.layer z.2 (fun l hl => ?_) (k := k) ?_
  · exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨l, hl⟩)
  · simpa using congrArg Subtype.val hk

end Base

section CaseA

variable {V : Type} [CommGroup V] [Finite V] {G T Y L : Subgroup (MulAut V)} {t : MulAut V}

theorem TenCfg.false_of_ge_eight (hc : TenCfg G T Y t L) {N : ℕ} (hN : 8 ≤ N)
    (A : TenAlt L Y N) : False := by
  classical
  have hZ := hc.noCentralTwo
  obtain ⟨ι, hcι⟩ : ∃ ι : Fin 8 ↪ Fin N,
      (A.c : Equiv.Perm (Fin N)) = viaEmbeddingHom ι (Equiv.swap 0 1 * Equiv.swap 1 2) :=
    exists_embedding_threeCycle (k := 5) (by omega) A.c3
  obtain ⟨hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8⟩ := caseA_perm_facts
  set E := viaEmbeddingHom ι with hE
  have hEinj : Function.Injective E := Equiv.Perm.viaEmbeddingHom_injective ι
  have hu_alt : E (Equiv.swap 3 4 * Equiv.swap 5 6) ∈ alternatingGroup (Fin N) := by
    rw [Equiv.Perm.mem_alternatingGroup, sign_viaEmbeddingHom]; exact hf3
  have hg_alt : E (Equiv.swap 2 7 * Equiv.swap 3 4) ∈ alternatingGroup (Fin N) := by
    rw [Equiv.Perm.mem_alternatingGroup, sign_viaEmbeddingHom]; exact hf4
  obtain ⟨xu, hxu⟩ := A.exists_lift hu_alt
  obtain ⟨xg, hxg⟩ := A.exists_lift hg_alt
  obtain ⟨y0, hy0Y, hy0c⟩ := A.exists_y
  have huu : lpi L xu * lpi L xu = 1 := by
    apply A.eps_injective
    rw [map_mul, hxu, map_one, ← map_mul, hf5, map_one]
  obtain ⟨s, hs2, hsπ⟩ := hZ.exists_lift huu
  have hs1 : s ≠ 1 := by
    intro h
    have h1 := congrArg A.eps hsπ
    rw [h, map_one, map_one, hxu] at h1
    exact hf6 (hEinj (by rw [map_one]; exact h1.symm))
  have hsε : A.eps (lpi L s) = E (Equiv.swap 3 4 * Equiv.swap 5 6) := by rw [hsπ, hxu]
  have hcu : Commute (A.c : Equiv.Perm (Fin N)) (E (Equiv.swap 3 4 * Equiv.swap 5 6)) := by
    rw [hcι]
    show E _ * E _ = E _ * E _
    rw [← map_mul, ← map_mul, ← hf1]
  have hYs : ∀ y ∈ Y, ∀ hyL : y ∈ L, (⟨y, hyL⟩ : ↥L) * s = s * ⟨y, hyL⟩ := by
    intro y hy hyL
    apply hZ.comm_of hs2
    apply A.eps_injective
    obtain ⟨m, hm⟩ := A.eps_mem_zpowers (y := ⟨y, hyL⟩) hy
    rw [map_mul, map_mul, hm, hsε]
    exact (hcu.zpow_left m).eq
  have hsG : (s : MulAut V) ∈ G ⊓ Subgroup.centralizer (Y : Set (MulAut V)) :=
    ⟨hc.layer.le s.2, Subgroup.mem_centralizer_iff.mpr fun h hh =>
      congrArg Subtype.val (hYs h hh (hc.hYL hh))⟩
  have hs1' : (s : MulAut V) ≠ 1 := fun h => hs1 (Subtype.ext h)
  have hs2' : (s : MulAut V) ^ 2 = 1 := by
    have := congrArg Subtype.val hs2
    simpa [pow_two] using this
  have hy03 : ((y0 : ↥L) : MulAut V) ^ 3 = 1 := (hc.cfg.sec5 hc.hV).pow_three hy0Y
  obtain ⟨R, hR⟩ := hc.cfg.twistData hy0Y hy03 hsG hs1' hs2'
  have hxgs : xg * s = s * xg := by
    apply hZ.comm_of hs2
    apply A.eps_injective
    rw [map_mul, map_mul, hxg, hsε, ← map_mul, ← map_mul, hf2]
  have hxgs' : (xg : MulAut V) * s = s * xg := congrArg Subtype.val hxgs
  set gG : ↥G := ⟨xg, hc.layer.le xg.2⟩ with hgG
  have hcomm : gG * ⟨s, hsG.1⟩ = ⟨s, hsG.1⟩ * gG := Subtype.ext hxgs'
  have hconj := hR.Rn gG hcomm _ hR.yR
  have hw := R.mul_mem hR.yR hconj
  obtain ⟨k, hk⟩ := hR.R3 ⟨_, hw⟩
  have hk' : (((y0 : ↥L) : MulAut V) * ((xg : MulAut V) * (y0 : MulAut V) * (xg : MulAut V)⁻¹)) ^
      3 ^ k = 1 := by
    have := congrArg (fun z : ↥R => ((z : ↥G) : MulAut V)) hk
    simpa using this
  have hwk : (y0 * (xg * y0 * xg⁻¹)) ^ 3 ^ k = 1 := Subtype.ext (by simpa using hk')
  have hwε : A.eps (lpi L (y0 * (xg * y0 * xg⁻¹))) = E ((Equiv.swap 0 1 * Equiv.swap 1 2) *
      ((Equiv.swap 2 7 * Equiv.swap 3 4) * (Equiv.swap 0 1 * Equiv.swap 1 2) *
        (Equiv.swap 2 7 * Equiv.swap 3 4)⁻¹)) := by
    simp only [map_mul, map_inv, hy0c, hxg, hcι]
  have hpow : (E ((Equiv.swap 0 1 * Equiv.swap 1 2) *
      ((Equiv.swap 2 7 * Equiv.swap 3 4) * (Equiv.swap 0 1 * Equiv.swap 1 2) *
        (Equiv.swap 2 7 * Equiv.swap 3 4)⁻¹))) ^ 3 ^ k = 1 := by
    rw [← hwε, ← map_pow, ← map_pow, hwk, map_one, map_one]
  have hord2 : orderOf (E ((Equiv.swap 0 1 * Equiv.swap 1 2) *
      ((Equiv.swap 2 7 * Equiv.swap 3 4) * (Equiv.swap 0 1 * Equiv.swap 1 2) *
        (Equiv.swap 2 7 * Equiv.swap 3 4)⁻¹))) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, pow_two, hf7, map_one]
    · intro h
      exact hf8 (hEinj (by rw [h, map_one]))
  have hdvd : 2 ∣ 3 ^ k := hord2 ▸ orderOf_dvd_of_pow_eq_one hpow
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_two hdvd
  omega

end CaseA

end CFSG.CGT.PushingUpLit.CGT6
