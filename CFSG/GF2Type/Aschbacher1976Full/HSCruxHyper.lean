module

public import CFSG.GF2Type.Aschbacher1976Full.HSCruxInterfaces
public import CFSG.GF2Type.Aschbacher1976Full.HSEmbedFacts

public section

namespace CFSG.GF2Type.Aschbacher1976Full.HS

open CFSG CFSG.Blueprint Subgroup PartC
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

open Classical in
noncomputable def sqBit (z x : G) : ZMod 2 := if x ^ 2 = z then 1 else 0

section Sigma

variable {z : G} {F : Subgroup G}

theorem sq_mul_eq (hF : Width.CData z F) {x y : G} (hx : x ∈ F) (hy : y ∈ F) :
    (x * y) ^ 2 = ⁅x, y⁆ * x ^ 2 * y ^ 2 := by
  have hx2 : y * x ^ 2 = x ^ 2 * y := by
    rcases hF.sq x hx with h | h
    · rw [h]; simp
    · rw [h]; exact (hF.zc y hy).symm
  calc (x * y) ^ 2 = ⁅x, y⁆ * (y * x ^ 2 * y) := by
        simp only [commutatorElement_def, pow_two]
        group
    _ = ⁅x, y⁆ * x ^ 2 * y ^ 2 := by
        rw [hx2, pow_two y]
        group

theorem sqBit_mul (hF : Width.CData z F) {x y : G} (hx : x ∈ F) (hy : y ∈ F) :
    sqBit z (x * y) = sqBit z x + sqBit z y + Width.cbit z x y := by
  have hzz : z * z = 1 := Width.zz_eq hF
  have hz1 : z ≠ 1 := hF.z1
  have h1 := sq_mul_eq hF hx hy
  have hcc : ⁅x, y⁆ = 1 ∨ ⁅x, y⁆ = z := hF.comm x hx y hy
  rcases hF.sq x hx with hx2 | hx2 <;> rcases hF.sq y hy with hy2 | hy2 <;>
    rcases hcc with hc | hc <;>
    simp [sqBit, Width.cbit, h1, hx2, hy2, hc, hzz, hz1, hz1.symm] <;> decide

theorem sqBit_one (hF : Width.CData z F) : sqBit z (1 : G) = 0 := by
  have hz1 : z ≠ 1 := hF.z1
  simp [sqBit, hz1.symm]

theorem sqBit_of_sq_eq_one (hF : Width.CData z F) {x : G} (hx : x ^ 2 = 1) : sqBit z x = 0 := by
  have hz1 : z ≠ 1 := hF.z1
  simp [sqBit, hx, hz1.symm]

theorem sqBit_of_sq_eq (hF : Width.CData z F) {x : G} (hx : x ^ 2 = z) : sqBit z x = 1 := by
  simp [sqBit, hx]

theorem sqBit_conj (hF : Width.CData z F) {x h : G} (hxF : x ∈ F) (hh : h ∈ Hz z) :
    sqBit z (h * x * h⁻¹) = sqBit z x := by
  have hhz : h * z = z * h := Subgroup.mem_centralizer_singleton_iff.mp hh
  have hzh : h * z * h⁻¹ = z := by rw [hhz]; group
  have hsq : (h * x * h⁻¹) ^ 2 = h * x ^ 2 * h⁻¹ := by rw [conj_pow]
  rcases hF.sq x hxF with h2 | h2
  · rw [sqBit_of_sq_eq_one hF h2, sqBit_of_sq_eq_one hF (by rw [hsq, h2]; group)]
  · rw [sqBit_of_sq_eq hF h2, sqBit_of_sq_eq hF (by rw [hsq, h2, hzh])]

end Sigma

section Main

variable {z k : G}

theorem exists_cruxE_of_quad (hset : HSSetting G z) (hti : HSTI z) (hk : ZF z = Subgroup.zpowers k)
    {θ : G → ZMod 2} (hθ : QuadFun z θ) : ∃ E : Subgroup G, IsCruxE z k E := by
  obtain ⟨⟨_, _, hz, hsymp⟩, hZ4⟩ := hset
  have hF2 : IsPGroup 2 ↥(Fz z) := hsymp.1
  obtain ⟨Z, A, hD⟩ := Width.exists_Z4Data hZ4
  have hF : Width.CData z (Fz z) := Embed.cdata_Fz hD hz
  obtain ⟨hθ1, hθ2, hθ3, hθ4⟩ := hθ
  obtain ⟨-, hk2⟩ := gen_props hD hz hF2 (IsConj.refl z) hk
  have hkZ : k ∈ ZF z := hk ▸ Subgroup.mem_zpowers k
  have hzZ : z ∈ ZF z := by rw [ZF_z hD hz hF2]; exact hD.mem_z
  have hkF : k ∈ Fz z := by
    rw [← hD.sup_eq]
    exact Subgroup.mem_sup_left (by rw [← ZF_z hD hz hF2]; exact hkZ)
  have hθone : θ 1 = 0 := by
    have h := hθ1 1 (Fz z).one_mem 1 (Fz z).one_mem
    rw [mul_one, Width.cbit_self, add_zero] at h
    revert h
    generalize θ 1 = a
    revert a
    decide
  set lam : G → ZMod 2 := fun x => sqBit z x + θ x with hlam
  have lam_one : lam 1 = 0 := by simp [hlam, sqBit_one hF, hθone]
  have lam_mul : ∀ x ∈ Fz z, ∀ y ∈ Fz z, lam (x * y) = lam x + lam y := by
    intro x hx y hy
    simp only [hlam]
    rw [sqBit_mul hF hx hy, hθ1 x hx y hy]
    generalize sqBit z x = a
    generalize sqBit z y = b
    generalize θ x = c
    generalize θ y = d
    generalize Width.cbit z x y = e
    revert a b c d e
    decide
  let E : Subgroup G :=
    { carrier := {x | x ∈ Fz z ∧ lam x = 0}
      one_mem' := ⟨(Fz z).one_mem, lam_one⟩
      mul_mem' := fun {a b} ha hb =>
        ⟨(Fz z).mul_mem ha.1 hb.1, by rw [lam_mul a ha.1 b hb.1, ha.2, hb.2]; rfl⟩
      inv_mem' := fun {a} ha => ⟨(Fz z).inv_mem ha.1, by
        have h := lam_mul a ha.1 a⁻¹ ((Fz z).inv_mem ha.1)
        rw [mul_inv_cancel, lam_one, ha.2, zero_add] at h
        exact h.symm⟩ }
  have hlamk : lam k = 1 := by
    have h1 : θ k = 0 := by
      have := hθ2 1 (Fz z).one_mem k hkZ
      rwa [one_mul, hθone] at this
    simp only [hlam]
    rw [sqBit_of_sq_eq hF hk2, h1]
    rfl
  refine ⟨E, fun x hx => hx.1, fun h hh e he => ⟨Width.Fz_conj_mem hh he.1, ?_⟩, ⟨hF.zF, ?_⟩,
    fun hkE => ?_, fun x hx => ?_, fun d hd => ?_⟩
  · simp only [hlam]
    rw [sqBit_conj hF he.1 hh, hθ3 h hh e he.1]
    exact he.2
  · have h1 : θ z = 0 := by
      have := hθ2 1 (Fz z).one_mem z hzZ
      rwa [one_mul, hθone] at this
    have hz2 : z ^ 2 = 1 := Width.z_sq hz
    simp only [hlam]
    rw [sqBit_of_sq_eq_one hF hz2, h1]
    rfl
  · have := hkE.2
    rw [hlamk] at this
    exact absurd this (by decide)
  · by_cases hx0 : lam x = 0
    · exact Subgroup.mem_sup_right ⟨hx, hx0⟩
    · have hx1 : lam x = 1 := by
        revert hx0
        generalize lam x = a
        revert a
        decide
      have hlk : lam k⁻¹ = 1 := by
        have h := lam_mul k hkF k⁻¹ ((Fz z).inv_mem hkF)
        rw [mul_inv_cancel, lam_one, hlamk] at h
        revert h
        generalize lam k⁻¹ = a
        revert a
        decide
      have hxk : x * k⁻¹ ∈ E := by
        refine ⟨(Fz z).mul_mem hx ((Fz z).inv_mem hkF), ?_⟩
        rw [lam_mul x hx k⁻¹ ((Fz z).inv_mem hkF), hx1, hlk]
        rfl
      have : x = (x * k⁻¹) * k := by group
      rw [this, sup_comm]
      exact Subgroup.mul_mem_sup hxk (Subgroup.mem_zpowers k)
  · have hdF : d ∈ Fz z := (hti.2 d hd).1
    obtain ⟨-, -, -, hd2, -⟩ := ZF_props hD hz hF2 hd.1
    refine ⟨hdF, ?_⟩
    simp only [hlam]
    rw [sqBit_of_sq_eq_one hF hd2, hθ4 d hd]
    rfl

end Main


end CFSG.GF2Type.Aschbacher1976Full.HS
