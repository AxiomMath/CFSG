module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11SingleXRho

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

namespace S11sCtx

variable {G : Type} [Group G] [Finite G] {t z : G} {K1 K2 T R : Subgroup G}
  {ρ : ↥R →* MulAut ↥(K1 ⊔ K2)} {a x : G} (c : S11sCtx t z K1 K2 T R ρ a x)

include c

theorem sign_D {g : G} (hgR : g ∈ R) (hg : g ∈ secD K1 K2 R) :
    Equiv.Perm.sign (c.pair.theta (ρ ⟨g, hgR⟩)) = 1 := by
  rw [c.rho_D ⟨g, hgR⟩ hg, map_one, Equiv.Perm.sign_one]

theorem sign_Q {g : G} (hgR : g ∈ R) (hg : g ∈ secQ K1 K2) :
    Equiv.Perm.sign (c.pair.theta (ρ ⟨g, hgR⟩)) = 1 := by
  have hgK : g ∈ K1 ⊔ K2 := c.set.split.Q_le hg
  rw [c.rho_K ⟨g, hgR⟩ hgK]
  exact c.pair.s11s_sign_conj ⟨g, hgK⟩

theorem sign_a (ha : a ∈ R) : Equiv.Perm.sign (c.pair.theta (ρ ⟨a, ha⟩)) = 1 := by
  exact c.pair.s11s_sign_swap (c.rho_a_sq ha) (c.rho_a12 ha)

theorem sign_x (hx : x ∈ R) : Equiv.Perm.sign (c.pair.theta (ρ ⟨x, hx⟩)) = 1 := by
  refine c.pair.s11s_sign_outer
    (c.rho_keep le_sup_left ⟨x, hx⟩ c.x_out1.1)
    (c.rho_keep le_sup_right ⟨x, hx⟩ c.x_out2.1)
    (c.rho_outer le_sup_left ⟨x, hx⟩ (fun n hn => c.T_N0 c.x_T hn) c.x_out1)
    (c.rho_outer le_sup_right ⟨x, hx⟩ (fun n hn => c.T_N0 c.x_T hn) c.x_out2)

theorem sign_TD {g : G} (hgR : g ∈ R) (hg : g ∈ T ⊔ secD K1 K2 R) :
    Equiv.Perm.sign (c.pair.theta (ρ ⟨g, hgR⟩)) = 1 := by
  let χ : ↥R →* ℤˣ := Equiv.Perm.sign.comp (c.pair.theta.comp ρ)
  let X : Subgroup G := χ.ker.map R.subtype
  have hX : ∀ g (hgR : g ∈ R),
      Equiv.Perm.sign (c.pair.theta (ρ ⟨g, hgR⟩)) = 1 → g ∈ X := by
    intro g hgR hg
    change g ∈ χ.ker.map R.subtype
    rw [Subgroup.mem_map]
    exact ⟨⟨g, hgR⟩, (MonoidHom.mem_ker).2
      (by simpa only [χ, MonoidHom.comp_apply] using hg), rfl⟩
  have hTD : T ⊔ secD K1 K2 R ≤ X := by
    refine sup_le ?_ ?_
    · rw [c.gen]
      refine (Subgroup.closure_le X).2 ?_
      rintro y ((hy | hy) | hy)
      · exact hX y (c.T_R hy.2) (sign_D c (c.T_R hy.2) ⟨hy.1, c.T_R hy.2⟩)
      · exact hX y (c.T_R (c.Q_T hy)) (sign_Q c (c.T_R (c.Q_T hy)) hy)
      · rcases hy with rfl | rfl
        · exact hX _ (c.T_R c.a_T) (sign_a c (c.T_R c.a_T))
        · exact hX _ (c.T_R c.x_T) (sign_x c (c.T_R c.x_T))
    · intro y hy
      exact hX y hy.2 (sign_D c hy.2 hy)
  have hgX : g ∈ X := hTD hg
  change g ∈ χ.ker.map R.subtype at hgX
  obtain ⟨r, hr, hrg⟩ := Subgroup.mem_map.mp hgX
  have hr1 : χ r = 1 := (MonoidHom.mem_ker).1 hr
  have hrg' : r = ⟨g, hgR⟩ := Subtype.ext hrg
  rw [← hrg']
  simpa only [χ, MonoidHom.comp_apply] using hr1

end S11sCtx

end CFSG.OddStandard.SmallF3.Omega
