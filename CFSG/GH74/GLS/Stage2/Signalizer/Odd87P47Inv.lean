module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P47InvA
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P47InvB
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P47FldStmt

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Matrix Subgroup CFSG CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.GH74.KGroups.L3Eps CFSG.Blueprint
  CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement

section Graph

variable {F : Type} [Field F]

theorem p47_no_graph (α : MulAut (projectiveSL 3 F)) (A : GL (Fin 3) F) (σ : F ≃+* F)
    (hα : α = conjAut 3 F A * fieldAut 3 F σ * dualAut 3 F) (Xh : Subgroup (projectiveSL 3 F))
    (hcl : Xh = (radP F).map (proj 3 F) ∨ Xh = (radM F).map (proj 3 F))
    (hmap : ∀ y ∈ Xh, α y ∈ Xh) : False := by
  rcases hcl with rfl | rfl
  · refine no_graph_of_maps_radP A σ (fun a b => ?_)
    have hm := hmap (proj 3 F (elP a b)) (Subgroup.mem_map_of_mem _ (mem_radP.2 ⟨a, b, rfl⟩))
    obtain ⟨g, hg, hgeq⟩ := Subgroup.mem_map.1 hm
    obtain ⟨a', b', rfl⟩ := mem_radP.1 hg
    exact ⟨a', b', by rw [← hα]; exact hgeq.symm⟩
  · refine no_graph_of_maps_radM A σ (fun a b => ?_)
    have hm := hmap (proj 3 F (elM a b)) (Subgroup.mem_map_of_mem _ (mem_radM.2 ⟨a, b, rfl⟩))
    obtain ⟨g, hg, hgeq⟩ := Subgroup.mem_map.1 hm
    obtain ⟨a', b', rfl⟩ := mem_radM.1 hg
    exact ⟨a', b', by rw [← hα]; exact hgeq.symm⟩

end Graph

theorem c_inv_mem_K (hfld : P47FieldCase) {G : Type} [Group G] {z : G} {k : Kind}
    (F4 : E4Facts G z k) {Y : Type} [Group Y] [Finite Y] {b : Y} (hY : SecOfG G z Y b)
    (hb2 : b * b = 1) {p : ℕ} {X : Subgroup Y} (hA : Sig4A b (⊤ : Subgroup Y) p X)
    (hop : pCore p Y = ⊥) (hc : C43c b p X) (hcp : C43cPlus p X) {e : Y} (he2 : e * e = 1)
    (hbe : e * b = b * e) (heX : e ∈ normalizer (X : Set Y)) : e ∈ ncl X := by
  classical
  have _ := hop
  have hp : p.Prime := hA.prime
  have hp2 : p ≠ 2 := hA.odd
  have : Fact p.Prime := ⟨hp⟩
  have hKn : (ncl X).Normal := Subgroup.normalClosure_normal
  obtain ⟨n, hn1, hLie, hXzK, -, -, -, -⟩ := hc
  have hXK : X ≤ ncl X := (le_sup_left : X ≤ X ⊔ zpowers b).trans hXzK
  have hbK : b ∈ ncl X := hXzK (Subgroup.mem_sup_right (Subgroup.mem_zpowers b))
  have hb1 : b ≠ 1 := by
    rintro rfl
    apply hA.ne_bot
    have h := hA.comm
    rw [Subgroup.zpowers_one_eq_bot, Subgroup.commutator_bot_right] at h
    exact h.symm
  obtain ⟨hcomp, hno, n', -, hLieHat⟩ := hcp
  have hoddZ : Odd (Nat.card ↥(Subgroup.center ↥(ncl X))) := p47_center_odd hLieHat
  obtain ⟨F, iF, fF, φ, hFcard, hs, hker, hφb⟩ := p47_exists_phi hbK hb2 hb1 hp hp2 hLie hoddZ
  have hpF : p ∣ Nat.card F := by
    rw [hFcard]
    exact dvd_pow_self p (by omega)
  have hchar : CharP F p := charP_of_dvd_card p hpF
  have h2 : (2 : F) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : F) = 0 := by exact_mod_cast h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
      ((CharP.cast_eq_zero_iff F p 2).mp h'))
  have hXinv : ∀ c : ↥(ncl X), (c : Y) * b = b * (c : Y) → (c : Y) ∈ normalizer (X : Set Y) :=
    fun c hc' => hA.inv c (Subgroup.mem_top _) (Subgroup.mem_centralizer_singleton_iff.2 hc')
  have hne := p47_map_ne_bot hcomp.1 φ hker
  have hclass := p47_classify hbK hb2 hXK hA.pgroup hXinv hoddZ h2 φ hs hker hφb hne
  let θ : MulAut ↥(ncl X) := MulAut.conjNormal e
  have hθapply : ∀ x : ↥(ncl X), ((θ x : ↥(ncl X)) : Y) = e * (x : Y) * e⁻¹ := fun x =>
    MulAut.conjNormal_apply e x
  have hθker : φ.ker.map θ.toMonoidHom = φ.ker := by
    rw [hker]
    exact CFSG.GH74.GLS.Stage2.Signalizer.L46E.AutC.map_center_eq_of_mulAut θ
  let α : MulAut (projectiveSL 3 F) :=
    CFSG.GH74.GLS.Stage2.Signalizer.L46E.AutC.inducedAut φ hs θ hθker
  have hαφ : ∀ x : ↥(ncl X), α (φ x) = φ (θ x) := fun x =>
    CFSG.GH74.GLS.Stage2.Signalizer.L46E.AutC.inducedAut_apply φ hs θ hθker x
  have hei : e⁻¹ = e := inv_eq_of_mul_eq_one_right he2
  have hαα : α * α = 1 := by
    ext h
    obtain ⟨x, rfl⟩ := hs h
    rw [MulAut.mul_apply, hαφ, hαφ, MulAut.one_apply]
    congr 1
    apply Subtype.ext
    rw [hθapply, hθapply, hei]
    calc e * (e * (x : Y) * e) * e = (e * e) * (x : Y) * (e * e) := by group
      _ = (x : Y) := by rw [he2]; group
  have hmap : ∀ y ∈ (X.subgroupOf (ncl X)).map φ, α y ∈ (X.subgroupOf (ncl X)).map φ := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hαφ]
    refine ⟨θ x, ?_, rfl⟩
    have hθx : ((θ x : ↥(ncl X)) : Y) ∈ X := by
      rw [hθapply]
      exact (Subgroup.mem_normalizer_iff.1 heX (x : Y)).1 hx
    exact hθx
  by_cases hα1 : α = 1
  · refine p47_mem_K_of_conj hcomp hno he2 hθapply (k₀ := 1) (fun x => ?_)
    have h1 : φ (θ x) = φ x := by rw [← hαφ, hα1, MulAut.one_apply]
    rw [← hker, MonoidHom.mem_ker, one_mul, inv_one, mul_one, map_mul, map_inv, h1,
      mul_inv_cancel]
  · rcases linear3_involution_cases h2 α hαα hα1 with ⟨y, -, -, hy⟩ | ⟨A, σ, hσ, hAσ⟩ |
      ⟨B, -, hB⟩ | ⟨A, σ, -, hAσ⟩
    · obtain ⟨k₀, hk₀⟩ := hs y
      refine p47_mem_K_of_conj hcomp hno he2 hθapply (k₀ := k₀) (fun x => ?_)
      have h1 : φ (θ x) = φ (k₀ * x * k₀⁻¹) := by
        calc φ (θ x) = α (φ x) := (hαφ x).symm
          _ = y * φ x * y⁻¹ := by rw [hy, MulAut.conj_apply]
          _ = φ (k₀ * x * k₀⁻¹) := by rw [← hk₀, map_mul, map_mul, map_inv]
      rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, h1, mul_inv_cancel]
    · by_cases he1 : e = 1
      · rw [he1]
        exact Subgroup.one_mem _
      · exfalso
        exact hfld G z k F4 Y b hY p hp hp2 (ncl X) (Subgroup.isPerfect_iff.mp hcomp.1.1) F
          ⟨n, hn1, hFcard⟩ φ hs hker hoddZ hbK e he2 he1
          (fun x => hKn.conj_mem (x : Y) x.2 e) hbe α
          (fun x hx => by
            rw [hαφ x]
            congr 1) A σ hσ hAσ
    · exact (p47_no_graph α B 1 (by rw [map_one, mul_one]; exact hB) _ hclass hmap).elim
    · exact (p47_no_graph α A σ hAσ _ hclass hmap).elim

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
