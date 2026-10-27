module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Assemble
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M22TNum
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M22TModel
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M22TRank
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1TightMod

public section

namespace CFSG.QuasithinUnique.Setup.X1

open CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu CFSG.Blueprint CFSG.Quasithin
  CFSG.QuasithinUnique.Setup.Family

theorem orderOf_conj_A (g z : ↥m22A) : orderOf (g⁻¹ * z * g) = orderOf z := by
  have := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) z
  simpa [MulAut.conj_apply] using this

theorem m22TightProp
    : M22TightProp := by
  intro W _ _ hW L E hq hirr hiso hEn hEne hEel hquad hEL hEcard hidx
  obtain ⟨e⟩ := hiso
  have e' : CQ L ≃* S22 := e
  obtain ⟨hWcard, hcent⟩ := tight_numerics hW hq hirr e' hEn hEel hEcard hidx
  have hperf : Group.IsPerfect ↥L := hq.1
  obtain ⟨ι, hιinj, hιE, hιX, hιL⟩ := exists_model hW hperf hirr hEn hEel e' hcent hEL
  let Ê : Subgroup ↥m22A := E.comap ι
  have hÊmem : ∀ x, x ∈ Ê ↔ ι x ∈ E := fun x => Iff.rfl
  have hÊcard : Nat.card Ê = 32 := by
    have h : Nat.card Ê = Nat.card E := by
      refine Nat.card_congr (Equiv.ofBijective (fun x : Ê => (⟨ι x, x.2⟩ : E)) ⟨?_, ?_⟩)
      · intro a b h
        exact Subtype.ext (hιinj (congrArg Subtype.val h))
      · rintro ⟨y, hy⟩
        obtain ⟨a, ha⟩ := hιE y hy
        exact ⟨⟨a, by rw [hÊmem, ha]; exact hy⟩, Subtype.ext ha⟩
    rw [h, hEcard]
    norm_num
  have hÊcomm : ∀ x ∈ Ê, ∀ y ∈ Ê, x * y = y * x := by
    intro x hx y hy
    apply hιinj
    rw [map_mul, map_mul]
    exact hEel.1 _ hx _ hy
  have hÊsq : ∀ x ∈ Ê, x * x = 1 := by
    intro x hx
    apply hιinj
    rw [map_mul, map_one]
    have := hEel.2 _ hx
    rwa [sq] at this
  obtain ⟨g, hg⟩ := a2_unique32 Ê hÊcomm hÊsq hÊcard
  let φ : ↥m22A →* MulAut W := ι.comp (MulAut.conj g⁻¹).toMonoidHom
  have hφ : ∀ x, φ x = ι (g⁻¹ * x * g) := by
    intro x
    simp [φ]
  have hφinj : Function.Injective φ := hιinj.comp (MulAut.conj g⁻¹).injective
  have hE5φ : E = E5.map φ := by
    ext x
    constructor
    · intro hx
      obtain ⟨a, ha⟩ := hιE x hx
      have haÊ : a ∈ Ê := by rw [hÊmem, ha]; exact hx
      refine ⟨g * a * g⁻¹, (hg a).1 haÊ, ?_⟩
      rw [hφ]
      have : g⁻¹ * (g * a * g⁻¹) * g = a := by group
      rw [this]
      exact ha
    · rintro ⟨y, hy, rfl⟩
      rw [hφ]
      have h1 : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
      have : g⁻¹ * y * g ∈ Ê := (hg _).2 (by rw [h1]; exact hy)
      exact this
  have hEgen : E = Subgroup.closure (Set.range fun i : Fin 5 => φ (bE i)) := by
    rw [hE5φ, E5_eq_closure, MonoidHom.map_closure, ← Set.range_comp]
    rfl
  obtain ⟨hb2, hbc, hcb, hdb, hc5, hc1, hd4, hdc, hct, hdt⟩ := a2_rel_check
  obtain ⟨hyT1, hyT2, hy01, hy02⟩ := a2_wit_check
  obtain ⟨hx2, hx4, hx2ne, hx4ne⟩ := a2_inner_check
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have hordT : orderOf (tE * (yT * tE * yT⁻¹)) = 11 := orderOf_eq_prime hyT1 hyT2
  have hord0 : orderOf (bE 0 * (y0 * bE 0 * y0⁻¹)) = 11 := orderOf_eq_prime hy01 hy02
  refine Tight.tight_core hW E hquad hWcard hidx (fun i => φ (bE i)) hEgen (φ cE) (φ dE)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro i
    rw [← map_inv, ← map_mul, ← map_mul]
    exact congrArg φ (hcb i)
  · intro i
    rw [← map_inv, ← map_mul, ← map_mul]
    exact congrArg φ (hdb i)
  · rw [← map_pow, hc5, map_one]
  · intro h
    exact hc1 (hφinj (h.trans (map_one φ).symm))
  · rw [← map_pow, hd4, map_one]
  · rw [← map_inv, ← map_mul, ← map_pow, ← map_mul]
    exact congrArg φ hdc
  · have := congrArg φ hct
    simp only [tE, map_mul, map_inv] at this
    exact this
  · have := congrArg φ hdt
    simp only [tE, map_mul, map_inv] at this
    exact this
  ·
    show 2 ^ 5 ≤ (fixV (Subgroup.zpowers (φ (bE 0) * φ (bE 1) * φ (bE 2) * φ (bE 3) *
      φ (bE 4)))).index
    have h := outer_rank hW hEn e' ι hιX (g⁻¹ * tE * g) (g⁻¹ * yT * g)
      (by
        have : g⁻¹ * tE * g * (g⁻¹ * yT * g * (g⁻¹ * tE * g) * (g⁻¹ * yT * g)⁻¹) =
            g⁻¹ * (tE * (yT * tE * yT⁻¹)) * g := by group
        rw [this, orderOf_conj_A, hordT])
    have e1 : φ (bE 0) * φ (bE 1) * φ (bE 2) * φ (bE 3) * φ (bE 4) = ι (g⁻¹ * tE * g) := by
      rw [← hφ]
      simp only [tE, map_mul]
    rw [e1]
    exact h
  · show 2 ^ 5 ≤ (fixV (Subgroup.zpowers (φ (bE 0)))).index
    have h := outer_rank hW hEn e' ι hιX (g⁻¹ * bE 0 * g) (g⁻¹ * y0 * g)
      (by
        have : g⁻¹ * bE 0 * g * (g⁻¹ * y0 * g * (g⁻¹ * bE 0 * g) * (g⁻¹ * y0 * g)⁻¹) =
            g⁻¹ * (bE 0 * (y0 * bE 0 * y0⁻¹)) * g := by group
        rw [this, orderOf_conj_A, hord0])
    rw [← hφ] at h
    exact h
  · show 2 ^ 4 ≤ (fixV (Subgroup.zpowers (φ (bE 0) * φ (bE 1)))).index
    have hz : bE 0 * bE 1 ∈ E5 := E5.mul_mem (bE_mem_E5 0) (bE_mem_E5 1)
    have hM : ((g⁻¹ * (bE 0 * bE 1) * g : ↥m22A) : Equiv.Perm (Fin 22)) ∈ NativeSporadic.M22 := by
      have h1 : ((bE 0 * bE 1 : ↥m22A) : Equiv.Perm (Fin 22)) ∈ NativeSporadic.M22 := by
        rw [← hx2]; exact x2M.2
      have := A_norm' g.2 _ h1
      simpa using this
    have h := inner_rank hW e' ι hirr hιinj hιL (g⁻¹ * (bE 0 * bE 1) * g) hM
      (by
        have : g⁻¹ * (bE 0 * bE 1) * g * (g⁻¹ * (bE 0 * bE 1) * g) =
            g⁻¹ * ((bE 0 * bE 1) * (bE 0 * bE 1)) * g := by group
        rw [this, sq_of_mem_E5 hz]; group)
      (by
        intro h1
        apply hx2ne
        have : bE 0 * bE 1 = g * (g⁻¹ * (bE 0 * bE 1) * g) * g⁻¹ := by group
        rw [this, h1]; group)
    have e1 : φ (bE 0) * φ (bE 1) = ι (g⁻¹ * (bE 0 * bE 1) * g) := by
      rw [← hφ, map_mul]
    rw [e1]
    exact h
  · show 2 ^ 4 ≤ (fixV (Subgroup.zpowers (φ (bE 0) * φ (bE 1) * φ (bE 2) * φ (bE 3)))).index
    have hz : bE 0 * bE 1 * bE 2 * bE 3 ∈ E5 :=
      E5.mul_mem (E5.mul_mem (E5.mul_mem (bE_mem_E5 0) (bE_mem_E5 1)) (bE_mem_E5 2)) (bE_mem_E5 3)
    have hM : ((g⁻¹ * (bE 0 * bE 1 * bE 2 * bE 3) * g : ↥m22A) : Equiv.Perm (Fin 22)) ∈
        NativeSporadic.M22 := by
      have h1 : ((bE 0 * bE 1 * bE 2 * bE 3 : ↥m22A) : Equiv.Perm (Fin 22)) ∈
          NativeSporadic.M22 := by
        rw [← hx4]; exact x4M.2
      have := A_norm' g.2 _ h1
      simpa using this
    have h := inner_rank hW e' ι hirr hιinj hιL (g⁻¹ * (bE 0 * bE 1 * bE 2 * bE 3) * g) hM
      (by
        have : g⁻¹ * (bE 0 * bE 1 * bE 2 * bE 3) * g * (g⁻¹ * (bE 0 * bE 1 * bE 2 * bE 3) * g) =
            g⁻¹ * ((bE 0 * bE 1 * bE 2 * bE 3) * (bE 0 * bE 1 * bE 2 * bE 3)) * g := by group
        rw [this, sq_of_mem_E5 hz]; group)
      (by
        intro h1
        apply hx4ne
        have : bE 0 * bE 1 * bE 2 * bE 3 =
            g * (g⁻¹ * (bE 0 * bE 1 * bE 2 * bE 3) * g) * g⁻¹ := by group
        rw [this, h1]; group)
    have e1 : φ (bE 0) * φ (bE 1) * φ (bE 2) * φ (bE 3) =
        ι (g⁻¹ * (bE 0 * bE 1 * bE 2 * bE 3) * g) := by
      rw [← hφ]
      simp only [map_mul]
    rw [e1]
    exact h

end CFSG.QuasithinUnique.Setup.X1
