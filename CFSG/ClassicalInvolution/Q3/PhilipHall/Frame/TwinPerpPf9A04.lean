module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf7A04
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf9Fuse
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf8H51
import CFSG.ClassicalInvolution.Q3.Q3T7P24EngB
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf9Ctx8Frame
import CFSG.ClassicalInvolution.Q3.Q3T7P24EngF04y

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Balance.Bootstrap
namespace T7K
open CFSG.ClassicalInvolution.Asc77.T7K
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' W : Subgroup G} {z u e g : G}

theorem conj_mem_sup (hs : Hyp23Setting Ω K K' z) {c : G}
    (hc : c ∈ Subgroup.centralizer ({z} : Set G)) {x : G} (hx : x ∈ K ⊔ K') :
    c * x * c⁻¹ ∈ K ⊔ K' := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.T7K.conj_mem_sup_of hs.stand.hyp hs.stand.mem hs.hz
    hs.hK' hs.hne hs.twinSet_eq hc hx
end T7K
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
@[expose] def C24_9_core : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [CoreLike G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z u : G)
    [Fact (CFSG.ClassicalInvolution.Q8P.P24.Hyp51TwinInnerAt Ω)],
    Hyp24 Ω K K' W S R R' z u → Nat.card ↥R = 8 → ¬ (S : Subgroup G) ≤ MGrp Ω W → False
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace S24B
open CFSG.ClassicalInvolution.Asc77.S24B

@[expose] def H3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [CoreLike G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z u : G)
    [Fact (CFSG.ClassicalInvolution.Q8P.P24.Hyp51TwinInnerAt Ω)],
    Hyp24 Ω K K' W S R R' z u → Nat.card ↥R = 8 →
    ∀ D : T7X.Frame24 Ω W, D.F.ρ.K = K → D.F.ρ'.K = K' → D.F.ρ.R = R → D.F.ρ'.R = R' →
      ∀ a : G, a * a = 1 → R ≤ Subgroup.centralizer ({a} : Set G) →
        R' ≤ Subgroup.centralizer ({a} : Set G) → ∀ T₃ : Subgroup G, IsSylow2In T₃ D.F.ρ₃.K →
        T₃ ≤ Subgroup.normalizer (W : Set G) → T₃ ≤ Subgroup.centralizer ({a} : Set G) → a = 1

@[expose] def NoGraph : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [CoreLike G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z u : G)
    [Fact (CFSG.ClassicalInvolution.Q8P.P24.Hyp51TwinInnerAt Ω)],
    Hyp24 Ω K K' W S R R' z u → Nat.card ↥R = 8 → ¬ (S : Subgroup G) ≤ MGrp Ω W →
      ∀ y ∈ (S : Subgroup G), TrivMu Ω W y → y ∈ Subgroup.centralizer (W : Set G)
end S24B
end Asc77

end

section

set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace T7X
open CFSG.ClassicalInvolution.Asc77.T7X
namespace Frame24
open CFSG.ClassicalInvolution.Asc77.T7X.Frame24
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {W : Subgroup G} (D : Asc77.T7X.Frame24 Ω W)
omit [Finite G] in

theorem x₁_mem : D.x₁ ∈ W := (D.h₁ ▸ Subgroup.mem_zpowers D.x₁ : D.x₁ ∈ D.F.ρ.R ⊓ W).2
omit [Finite G] in

theorem x₂_mem : D.x₂ ∈ W := (D.h₂ ▸ Subgroup.mem_zpowers D.x₂ : D.x₂ ∈ D.F.ρ'.R ⊓ W).2
omit [Finite G] in

theorem x₃_mem : D.x₃ ∈ W := (D.h₃ ▸ Subgroup.mem_zpowers D.x₃ : D.x₃ ∈ D.F.ρ₃.R ⊓ W).2

theorem comm13 : Commute D.x₁ D.x₃ :=
  Q3.Q3CL.Thompson.commutes_of_mem_WSet D.c.hΩ D.c.hW D.x₁ D.x₁_mem D.x₃ D.x₃_mem

theorem comm23 : Commute D.x₂ D.x₃ :=
  Q3.Q3CL.Thompson.commutes_of_mem_WSet D.c.hΩ D.c.hW D.x₂ D.x₂_mem D.x₃ D.x₃_mem
end Frame24
end T7X
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace S24B
open CFSG.ClassicalInvolution.Asc77.S24B
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem rep_mul_self {W : Subgroup G} (c : Q3.Q3CL.Thompson.Ctx Ω W) (ρ : Thompson.Rep Ω W) {z₀ : G}
    (hz : IsUniqueInvolution ρ.K z₀) : ρ.r * ρ.r = z₀ := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.Ctx8Frame.rep_mul_self c ρ hz

structure Ctx8F (Ω : Set (Subgroup G)) (K K' W : Subgroup G)
    (S : Sylow 2 G) (R R' : Subgroup G) (z u : G) : Type extends
    Ctx8 Ω K K' W S R R' z u where
  fuse : KKFuse → ∀ {u₁ u₂ : G}, u₁ ∈ K ⊔ K' → u₁ ≠ 1 → u₁ ≠ z → u₁ * u₁ = 1 →
    u₂ ∈ K ⊔ K' → u₂ ≠ 1 → u₂ ≠ z → u₂ * u₂ = 1 →
      ∃ c ∈ Subgroup.centralizer ({z} : Set G), c * u₁ * c⁻¹ = u₂
  hyp : Hyp24 Ω K K' W S R R' z u

theorem Ctx8F.nonempty [CoreLike G] {K K' W : Subgroup G} {S : Sylow 2 G}
    {R R' : Subgroup G} {z u : G} (hyp : Hyp24 Ω K K' W S R R' z u) (h8 : Nat.card ↥R = 8) :
    Nonempty (Ctx8F Ω K K' W S R R' z u) := by
  obtain ⟨C⟩ := Ctx8.nonempty hyp.std.setting hyp.data h8
  refine ⟨{ toCtx8 := C, fuse := ?_, hyp := hyp }⟩
  intro hF u₁ u₂ h₁ h₁1 h₁z h₁2 h₂ h₂1 h₂z h₂2
  exact hF G Ω K K' z hyp.std u₁ u₂ h₁ h₁1 h₁z h₁2 h₂ h₂1 h₂z h₂2

namespace Ctx8F
open CFSG.ClassicalInvolution.Asc77.S24B.Ctx8
variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (C : Asc77.S24B.Ctx8F Ω K K' W S R R' z u)

theorem m_eq_one : C.D.m = 1 := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.Ctx8Frame.m_eq_one C.toFrame

theorem orderOf_x₁ : orderOf C.D.x₁ = 4 := by rw [C.D.o₁, C.m_eq_one]

theorem orderOf_x₂ : orderOf C.D.x₂ = 4 := by rw [C.D.o₂, C.m_eq_one]

theorem orderOf_x₃ : orderOf C.D.x₃ = 4 := by rw [C.D.o₃, C.m_eq_one]

theorem x₁_sq : C.D.x₁ ^ 2 = z := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.Ctx8Frame.x₁_sq C.toFrame

theorem x₂_sq : C.D.x₂ ^ 2 = z := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.Ctx8Frame.x₂_sq C.toFrame

theorem x₃_sq : C.D.x₃ ^ 2 = C.D.F.j := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.Ctx8Frame.x₃_sq C.toFrame

theorem x₂_eq : C.D.x₂ = C.D.x₁ * C.D.x₃ ^ 2 := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.Ctx8Frame.x₂_eq C.toFrame

theorem j_eq : C.D.F.j = C.D.x₁⁻¹ * C.D.x₂ := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.Ctx8Frame.j_eq C.toFrame

theorem x₁_mem_R : C.D.x₁ ∈ R :=
  (congrArg (fun X => C.D.x₁ ∈ X) C.hR).mp
    (C.D.h₁ ▸ Subgroup.mem_zpowers C.D.x₁ : C.D.x₁ ∈ C.D.F.ρ.R ⊓ W).1

theorem x₂_mem_R' : C.D.x₂ ∈ R' :=
  (congrArg (fun X => C.D.x₂ ∈ X) C.hR').mp
    (C.D.h₂ ▸ Subgroup.mem_zpowers C.D.x₂ : C.D.x₂ ∈ C.D.F.ρ'.R ⊓ W).1

theorem x₃_mem_R₃ : C.D.x₃ ∈ C.D.F.ρ₃.R :=
  (C.D.h₃ ▸ Subgroup.mem_zpowers C.D.x₃ : C.D.x₃ ∈ C.D.F.ρ₃.R ⊓ W).1

theorem x₁_mem_K : C.D.x₁ ∈ K := C.hd.hR.2.1 C.x₁_mem_R

theorem x₂_mem_K' : C.D.x₂ ∈ K' := C.hd.hR'.2.1 C.x₂_mem_R'

theorem x₃_mem_J : C.D.x₃ ∈ C.D.F.ρ₃.K := C.D.F.ρ₃.hRK.1 C.x₃_mem_R₃

include C in

theorem hzK : IsUniqueInvolution K z := C.hs.hz
include C in

theorem hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet C.hs.hz C.hs.hK'

theorem hjJ : IsUniqueInvolution C.D.F.ρ₃.K C.D.F.j := C.D.F.hj

theorem z_ne_j : z ≠ C.D.F.j := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.Ctx8Frame.z_ne_j C.toFrame

theorem r_mul_self : C.D.F.ρ.r * C.D.F.ρ.r = z :=
  (rep_mul_self C.D.c C.D.F.ρ C.D.F.hz).trans C.hz

theorem r_mem_R : C.D.F.ρ.r ∈ R := (congrArg (fun X => C.D.F.ρ.r ∈ X) C.hR).mp C.D.F.ρ.hr

theorem t_mem_R' : C.D.F.ρ'.r ∈ R' := (congrArg (fun X => C.D.F.ρ'.r ∈ X) C.hR').mp C.D.F.ρ'.hr

include C in

theorem R_ne_R' : R ≠ R' := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.Ctx8Frame.R_ne_R' C.toFrame
include C in

theorem commutes_R_R' : Commutes R R' :=
  l6_7_proved G Ω C.hs.stand.hyp S R C.hd.hR.1 R' C.hd.hR'.1
    C.hd.hR.2.2 C.hd.hR'.2.2 C.R_ne_R'

theorem commute_r_t : Commute C.D.F.ρ.r C.D.F.ρ'.r :=
  C.commutes_R_R' _ C.r_mem_R _ C.t_mem_R'

theorem exists_nf {w : G} (hw : w ∈ W) : ∃ a b : ℤ, w = C.D.x₁ ^ a * C.D.x₃ ^ b := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.Ctx8Frame.exists_nf C.toFrame hw

theorem mul_nf (a b c d : ℤ) :
    C.D.x₁ ^ a * C.D.x₃ ^ b * (C.D.x₁ ^ c * C.D.x₃ ^ d) = C.D.x₁ ^ (a + c) * C.D.x₃ ^ (b + d) := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.mul_nf_of C.D.comm13 a b c d

theorem conj_r_nf (a b : ℤ) :
    C.D.F.ρ.r * (C.D.x₁ ^ a * C.D.x₃ ^ b) * C.D.F.ρ.r⁻¹ = C.D.x₁ ^ (b - a) * C.D.x₃ ^ b := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.Ctx8Frame.conj_r_nf C.toFrame a b

theorem conj_t_nf (a b : ℤ) :
    C.D.F.ρ'.r * (C.D.x₁ ^ a * C.D.x₃ ^ b) * C.D.F.ρ'.r⁻¹ =
      C.D.x₁ ^ (a + b) * C.D.x₃ ^ (3 * b) := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.Ctx8Frame.conj_t_nf C.toFrame a b

theorem eq_one_of_nf (a b : ℤ) (h : C.D.x₁ ^ a * C.D.x₃ ^ b = 1) :
    C.D.x₁ ^ a = 1 ∧ C.D.x₃ ^ b = 1 := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.Ctx8Frame.eq_one_of_nf C.toFrame a b h

theorem four_dvd_of_x₁ {a : ℤ} (h : C.D.x₁ ^ a = 1) : (4 : ℤ) ∣ a := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.Ctx8Frame.four_dvd_of_x₁ C.toFrame h

end Ctx8F
end S24B
end Asc77

end

end CFSG.ClassicalInvolution.Q8P
